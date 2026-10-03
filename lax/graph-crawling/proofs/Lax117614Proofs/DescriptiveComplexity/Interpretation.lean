/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Complexity
import Mathlib.Tactic.FinCases
import Lax117614.CrawlInstances
import Lax117614.GraphCrawlingProblem
import Lax117614.WebsiteGraphs
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

/-!
# First-order interpretations and FO reductions

Complexity theory is essentially absent from Mathlib because formalizing a
machine model of computation (and resource bounds on it) is hard. However, many
classical NP-hardness reductions do not need the full power of polynomial-time
computation: the reduction is *first-order expressible* – the output structure
can be described by fixed first-order formulas evaluated in the input
structure. Such FO reductions are computable in AC⁰ ⊆ LOGSPACE ⊆ PTIME, so
exhibiting an FO reduction is (much) stronger than exhibiting a Karp
reduction ([Karp 1972][karp1972reducibility]), while being completely
machine-model-free and therefore easy to
formalize on top of Mathlib's `ModelTheory` library.

This file defines:

* `Lax117614Proofs.DescriptiveComplexity.DecisionProblem L`: a “problem” over the vocabulary `L`, i.e., a
  property of `L`-structures;
* `Lax117614Proofs.DescriptiveComplexity.FOInterpretation L L' Tag dim`: a tagged, `dim`-dimensional
  first-order interpretation of a relational language `L'` in a language `L`,
  mapping every `L`-structure `A` to an `L'`-structure `I.Map A` with universe
  `Tag × (Fin dim → A)`;
* `Lax117614Proofs.DescriptiveComplexity.FOInterpretation.IsQuantifierFree`: interpretations all of whose
  defining formulas are quantifier-free (an even weaker reduction notion);
* `Lax117614Proofs.DescriptiveComplexity.FOReduction P Q`: an FO reduction from problem `P` to problem
  `Q`, i.e., an interpretation mapping yes-instances of `P` exactly to
  yes-instances of `Q`.

## Design notes

The textbook notion of FO reduction maps a structure `A` to a structure with
universe a definable subset of `A^k`, using a linear order on `A` to encode
constantly many “sorts” of elements. To stay order-free and subset-free we
instead tag tuples with elements of a finite type `Tag`, and use the full
universe `Tag × A^dim`: junk elements are harmless in practice because the
defining formulas can exclude them from all relations. Every tagged
interpretation can be converted into a textbook `k`-ary FO reduction on
ordered structures (using the order to encode constantly many tags), so the
notion formalized here is a genuine form of FO reducibility.

The universe of `I.Map A` is `Tag × (Fin dim → A)`, which is finite whenever
`A` and `Tag` are (`FOInterpretation.map_finite`): FO reductions map finite
structures to finite structures, as required for reductions between decision
problems on finite structures.

Following the usual convention of finite model theory, reductions are only
required to be correct on *nonempty* structures (and their tag types are
required to be nonempty, so that nonempty structures map to nonempty
structures). Empty structures are degenerate: no fixed-dimension
interpretation can produce a nonempty structure from an empty one, so e.g., no
problem that is false on an empty structure could reduce to SAT (whose empty
instance is trivially satisfiable), and hardness results would fail for
spurious reasons.
-/

namespace Lax117614Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L L' : Language.{0, 0})

namespace DecisionProblem

variable {L} [L.IsRelational]

@[ext]
theorem ext {P Q : Lax904597.Problems.DecisionProblem L} (h : ∀ (A : Type) [L.Structure A], P A ↔ Q A) :
    P = Q := by
  obtain ⟨p, hp⟩ := P
  obtain ⟨q, hq⟩ := Q
  have : p = q := funext fun A => funext fun inst => propext (h A)
  subst this
  rfl

end DecisionProblem

end Lax117614Proofs.DescriptiveComplexity

namespace Lax904597.Problems.DecisionProblem

export Lax117614Proofs.DescriptiveComplexity.DecisionProblem (ext)

end Lax904597.Problems.DecisionProblem

namespace Lax117614Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L L' : Language.{0, 0})

namespace DecisionProblem

variable {L} [L.IsRelational]

end DecisionProblem

/-! ### Transport of relations along isomorphisms

Proving the `iso_invariant` field of a `DecisionProblem` always starts the
same way: the semantic property is phrased in terms of `RelMap r ![a]` /
`RelMap r ![a, b]`, and one must know that these transport along an
`L`-isomorphism. The two lemmas below package this step once and for all
(`Mathlib`'s `StrongHomClass.map_rel` states it with `e ∘ ![a, b]`, which
must first be normalized to `![e a, e b]`). -/

section RelMapTransport

variable {L} {A B : Type} [L.Structure A] [L.Structure B]

/-- A unary relation transports along an `L`-isomorphism. -/
theorem relMap_equiv₁ (e : A ≃[L] B) (r : L.Relations 1) (a : A) :
    RelMap r ![a] ↔ RelMap r ![e a] := by
  have h := StrongHomClass.map_rel e r ![a]
  have hv : e ∘ ![a] = ![e a] := by
    funext j
    fin_cases j
    simp
  rw [hv] at h
  exact h.symm

/-- A binary relation transports along an `L`-isomorphism. -/
theorem relMap_equiv₂ (e : A ≃[L] B) (r : L.Relations 2) (a b : A) :
    RelMap r ![a, b] ↔ RelMap r ![e a, e b] := by
  have h := StrongHomClass.map_rel e r ![a, b]
  have hv : e ∘ ![a, b] = ![e a, e b] := by
    funext j
    fin_cases j <;> simp
  rw [hv] at h
  exact h.symm

end RelMapTransport

namespace FOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : Lax904597.Interpretations.FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

theorem relMap_map [L'.IsRelational] {n : ℕ} (R : L'.Relations n) (xs : Fin n → I.Map A) :
    RelMap R xs ↔ (I.relFormula R fun i => (xs i).1).Realize fun p => (xs p.1).2 p.2 :=
  Iff.rfl

end FOInterpretation

end Lax117614Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax117614Proofs.DescriptiveComplexity.FOInterpretation (relMap_map)

end Lax904597.Interpretations.FOInterpretation

namespace Lax117614Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L L' : Language.{0, 0})

namespace FOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : Lax904597.Interpretations.FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

omit [L.Structure A] in
/-- FO interpretations map finite structures to finite structures. -/
theorem map_finite [Finite Tag] [Finite A] : Finite (I.Map A) :=
  inferInstanceAs (Finite (Tag × (Fin dim → A)))

end FOInterpretation

end Lax117614Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation

export Lax117614Proofs.DescriptiveComplexity.FOInterpretation (map_finite)

end Lax904597.Interpretations.FOInterpretation

namespace Lax117614Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L L' : Language.{0, 0})

namespace FOInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

variable (I : Lax904597.Interpretations.FOInterpretation L L' Tag dim) (A : Type) [L.Structure A]

end FOInterpretation

variable {L L' : Language.{0, 0}}

@[inherit_doc]
scoped notation:50 P:51 " ≤ᶠᵒ " Q:51 => Lax904597.Interpretations.FOReduction P Q

end Lax117614Proofs.DescriptiveComplexity


