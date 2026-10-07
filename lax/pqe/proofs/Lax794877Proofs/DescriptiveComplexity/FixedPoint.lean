/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Dynamics.FixedPoints.Basic
import Lax794877Proofs.DescriptiveComplexity.SecondOrderHorn
import Lax794877Proofs.DescriptiveComplexity.SecondOrderHornPull
import Lax794877Proofs.DescriptiveComplexity.Padding
import Lax280166.CountingCliques
import Lax280166.CountingDominatingSets
import Lax280166.CountingFeedbackSets
import Lax280166.CountingHamiltonCircuits
import Lax280166.CountingKnapsacks
import Lax280166.CountingSatVariants
import Lax280166.CountingSetFamilies
import Lax280166.CountingSteinerTrees
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
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
import Lax794877.ExampleDatabase
import Lax794877.PossibleWorlds
import Lax794877.Queries
import Lax794877.WeightedWorlds
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
import Lax859101.CountingAllSets
import Lax859101.CountingBipartite
import Lax859101.CountingDnf
import Lax859101.CountingNaeSat
import Lax859101.CountingRestrictedSat
import Lax859101.OneCallReductions
import Lax859101.SubtractiveReductions
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax794877Proofs.DescriptiveComplexity.LFPDef
end Lax794877Proofs.DescriptiveComplexity.LFPDef

namespace Lax794877Proofs.DescriptiveComplexity.LFPDefinable
end Lax794877Proofs.DescriptiveComplexity.LFPDefinable

namespace Lax794877Proofs.DescriptiveComplexity.SigmaSOHornDefinable
end Lax794877Proofs.DescriptiveComplexity.SigmaSOHornDefinable

namespace Lax859101.SubtractiveReductions.FOInterpretation
end Lax859101.SubtractiveReductions.FOInterpretation

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornClause HornProgram SigmaSOHornDefinable)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax794877Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (Derives LFPDef LFPDefinable lfpAssign)
end Lax794877Proofs.DescriptiveComplexity

namespace Lax904597.Interpretations.FOInterpretation
export Lax859101.SubtractiveReductions.FOInterpretation (ordExtend)
end Lax904597.Interpretations.FOInterpretation

/-!
# FO(LFP): first-order logic with a least fixed point

The logic FO(LFP) ([Immerman 1986][immerman1986relational]; [Vardi
1982][vardi1982complexity]), in the clausal normal form this library uses for
kernels everywhere else: a `DescriptiveComplexity.LFPDef` bundles

* a block of relation variables and a finite list of *rules* deriving them –
  the same `DescriptiveComplexity.HornClause` data as an SO-Horn program, read here as
  an inductive definition rather than a constraint;
* an arbitrary first-order *output* sentence over the input vocabulary
  expanded by those variables, evaluated at the least fixed point.

## Why the output formula is the point

The fixed point is the same object in both logics – the least model of a set
of rules. What distinguishes FO(LFP) from SO-Horn is what one is allowed to
say *about* it. An SO-Horn program can only reject models, through goal
clauses, and a goal clause tests its atoms positively; FO(LFP) evaluates an
unrestricted first-order sentence, so it may negate fixed-point atoms.

That is exactly the closure that SO-Horn lacks: `DescriptiveComplexity.LFPDefinable` is
closed under complement by negating the output
(`DescriptiveComplexity.LFPDefinable.compl`, a one-liner), whereas the corresponding
statement for SO-Horn is open – see `DescriptiveComplexity.Problems.HornSat`. The
inclusion `DescriptiveComplexity.SigmaSOHornDefinable.lfpDefinable` transports every
SO-Horn definition into this logic, so PTIME as defined by the Horn fragment
sits inside FO(LFP) together with its complements.

## What is proved here, and where the equivalence is completed

`DescriptiveComplexity.SigmaSOHornDefinable.lfpDefinable` is one half of the equivalence
of the two formalisms: every SO-Horn definition is an FO(LFP) definition. The
other half – bringing an FO(LFP) definition back into the Horn fragment – is
the translation of `DescriptiveComplexity.FixedPointHorn`, built on the stage theory of
this file: the stages `DescriptiveComplexity.derivesIn` stabilize once the atom count is
reached (`DescriptiveComplexity.derivesIn_iff_derives_of_card_le`), so a stage indexed by
a large enough tuple stands in for the fixed point, and its *complement* can
be derived positively, one stage at a time. Together the two halves make the
notions interchangeable (`DescriptiveComplexity.lfpDefinable_iff_sigmaSOHornDefinable`)
and give `PiP 0 = SigmaP 0` (`DescriptiveComplexity.piP_zero_eq`).

The notion is also closed under (ordered) first-order reductions
(`DescriptiveComplexity.LFPDefinable.of_orderedReduction`), so it is class-worthy in the
sense of `DescriptiveComplexity.ComplexityClass`.

A second consumer of the stage theory is not formalized: a `Σ₁` definition,
giving `FO(LFP) ⊆ NP` directly, would *guess* a fixed point together with a
well-founded derivation order and check both first-order. The semantic key is
provided here – `DescriptiveComplexity.derives_eq_of_closed_of_wf` says that a relation
*closed* under the rules and *well-foundedly derivable* is exactly the least
fixed point, `DescriptiveComplexity.derives_step_of_depth` supplies the witnessing
order from the stages, and `DescriptiveComplexity.LFPDef.holds_iff_of_certificate`
packages this; the formulas themselves are not built. (The inclusion itself
follows by composing the translation with the Horn membership of
`DescriptiveComplexity.Problems.HornSat`.)

## The fixed point

Rather than a stage-indexed iteration, the least model is the inductive
predicate `DescriptiveComplexity.Derives`: a tuple is derived when some rule fires on
already-derived tuples. Being an inductive definition it comes with exactly the
two properties a least fixed point needs – it satisfies the rules
(`DescriptiveComplexity.lfpAssign_rule`) and it is contained in every assignment that
does (`DescriptiveComplexity.lfpAssign_least`).

Rules whose head is `none` derive nothing and are simply inert here, so an
SO-Horn program can be handed over unchanged: its goal clauses reappear in the
output formula.
-/

namespace Lax794877Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The least model of a rule system -/

section Derives

variable {Lg : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable {A : Type} [Lg.Structure A]

/-- The least fixed point satisfies every rule with a head. (A clause with no
head is a *constraint*, not a rule: it derives nothing, and is what the output
formula of `DescriptiveComplexity.LFPDef` takes over.) -/
theorem lfpAssign_rule {rules : List (Lax535992.HornFragment.HornClause Lg B k)}
    {c : Lax535992.HornFragment.HornClause Lg B k} (hc : c ∈ rules) {a : Lax485149.SecondOrderAtoms.SOAtom B k}
    (ha : c.head = some a) (v : Fin k → A) : c.Holds (Lax535992.LeastFixedPoint.lfpAssign rules) v := by
  rintro ⟨hg, hb⟩
  rw [Lax535992.HornFragment.HornClause.HeadHolds, ha, Option.elim_some]
  exact Lax535992.LeastFixedPoint.Derives.rule hc ha hg fun b hbmem => hb b hbmem

/-- **The least fixed point is contained in every prefixpoint**: in every
assignment closed under the rules. -/
theorem lfpAssign_least_of_closed {rules : List (Lax535992.HornFragment.HornClause Lg B k)}
    {ρ : B.Assignment A}
    (hρ : ∀ c ∈ rules, ∀ a : Lax485149.SecondOrderAtoms.SOAtom B k, c.head = some a → ∀ v : Fin k → A,
      c.guard.Realize v → (∀ b ∈ c.body, b.Holds ρ v) → a.Holds ρ v)
    {p : Σ i : B.ι, Fin (B.arity i) → A} (hp : Lax535992.LeastFixedPoint.Derives rules p) : ρ p.1 p.2 := by
  induction hp with
  | rule hc ha hg hb ih => exact hρ _ hc _ ha _ hg fun b hbmem => ih b hbmem

end Derives

/-! ### Stages, depth, and the certificate characterization

Putting FO(LFP) back into the Horn fragment, and certifying a fixed point in
`Σ₁`, both need the same thing: a way to say
“this relation *is* the least fixed point” that a *positive* formalism can
test. Closure alone is not enough (anything larger is closed too); what pins
the least fixed point down is closure together with *well-founded
derivability* – every element derived by a rule from strictly earlier
elements. That is `DescriptiveComplexity.derives_eq_of_closed_of_wf` below, and the
stages provide the witnessing order. -/

section Stages

variable {Lg : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable {A : Type} [Lg.Structure A]

/-- The atoms of a block over a structure: a relation variable and a tuple. -/
abbrev BAtom (B : Lax904597.SecondOrder.SOBlock) (A : Type) : Type := Σ i : B.ι, Fin (B.arity i) → A

/-! #### Depth, and the certificate -/

/-! #### Stabilization: the stages close within `Nat.card` many rounds

On a finite structure the stages are an increasing chain of subsets of the
finitely many atoms, so they stabilize by the time the atom count is reached
(`DescriptiveComplexity.exists_succ_eq_of_monotone_subset`, the one chain
pigeonhole of the library, in `DescriptiveComplexity.Iterate`) – after that many
rounds, `DescriptiveComplexity.derivesIn` *is* the least fixed point. This is
what lets a stage indexed by a large enough tuple stand in for the fixed point
itself in `DescriptiveComplexity.FixedPointHorn`. -/

end Stages

/-! ### The fixed point transports along isomorphisms -/

section Map

variable {Lg : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable {M N : Type} [Lg.Structure M] [Lg.Structure N]

/-- Derivability transports along an isomorphism of structures: the rules only
see the guards, which an isomorphism preserves. -/
theorem derives_map (e : M ≃[Lg] N) {rules : List (Lax535992.HornFragment.HornClause Lg B k)}
    {q : BAtom B M} (h : Lax535992.LeastFixedPoint.Derives rules q) :
    Lax535992.LeastFixedPoint.Derives rules (⟨q.1, fun j => e (q.2 j)⟩ : BAtom B N) := by
  induction h with
  | @rule c hc a ha v hg hb ih =>
    refine Lax535992.LeastFixedPoint.Derives.rule hc ha (v := fun j => e (v j)) ?_ fun b hbmem => ih b hbmem
    exact (StrongHomClass.realize_formula e c.guard).mpr hg

/-- The least fixed point transports along an isomorphism. -/
theorem lfpAssign_map (e : M ≃[Lg] N) (rules : List (Lax535992.HornFragment.HornClause Lg B k)) :
    Lax535992.LeastFixedPoint.lfpAssign (A := N) rules = B.mapAssign e.toEquiv (Lax535992.LeastFixedPoint.lfpAssign (A := M) rules) := by
  funext i x
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · have := derives_map e.symm h
    exact this
  · have h2 : Lax535992.LeastFixedPoint.Derives rules (⟨i, fun j => e (e.symm (x j))⟩ : BAtom B N) :=
      derives_map e (h : Lax535992.LeastFixedPoint.Derives rules ⟨i, fun j => e.symm (x j)⟩)
    have hx : (fun j => e (e.symm (x j))) = x := funext fun j => e.toEquiv.apply_symm_apply (x j)
    rw [hx] at h2
    exact h2

end Map

/-! ### The fixed point commutes with pullbacks

The least fixed point of the pulled rules is the pullback of the least fixed
point: both inclusions are an application of leastness, since each side is
closed under the other's rules (`DescriptiveComplexity.HornProgram.pull_holds`). This is
the fixed-point half of closure of `DescriptiveComplexity.LFPDefinable` under (ordered)
first-order reductions; what remains for that closure is to pull the *output*
sentence back, through `DescriptiveComplexity.FOInterpretation.extendSO` and
`DescriptiveComplexity.FOInterpretation.ordExtendLEquiv`, which is bookkeeping between
the three structures involved rather than mathematics. -/

section Pull

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {d : ℕ}

variable {B : Lax904597.SecondOrder.SOBlock} {k : ℕ} {A : Type} [L₁.Structure A]

theorem lfpAssign_pull (I : Lax904597.Interpretations.FOInterpretation L₁ L₂ Tag d)
    (rules : List (Lax535992.HornFragment.HornClause L₂ B k)) :
    Lax535992.LeastFixedPoint.lfpAssign (HornProgram.pull I rules) = B.pullAssign (Lax535992.LeastFixedPoint.lfpAssign rules (A := I.Map A)) := by
  funext p x
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · -- the pulled fixed point is contained in the pullback of the fixed point
    refine lfpAssign_least_of_closed (ρ := B.pullAssign (Lax535992.LeastFixedPoint.lfpAssign rules (A := I.Map A)))
      (fun c' hc' a' ha' w hg hb => ?_) h
    obtain ⟨c, hc, t, rfl⟩ := HornProgram.pull_cases I hc'
    have hcl : (c.pull I t).Holds (B.pullAssign (Lax535992.LeastFixedPoint.lfpAssign rules (A := I.Map A))) w := by
      refine (HornClause.pull_holds I c t (Lax535992.LeastFixedPoint.lfpAssign rules (A := I.Map A)) w).mpr ?_
      cases hh : c.head with
      | none => exact absurd ha' (by simp [HornClause.pull, hh])
      | some a => exact lfpAssign_rule hc hh _
    have hhead := hcl ⟨hg, hb⟩
    rwa [Lax535992.HornFragment.HornClause.HeadHolds, ha', Option.elim_some] at hhead
  · -- and conversely, by leastness on the interpreted side
    set σ : (B.pull Tag d).Assignment A := Lax535992.LeastFixedPoint.lfpAssign (HornProgram.pull I rules) with hσ
    have hsub : ∀ q : Σ i : B.ι, Fin (B.arity i) → I.Map A,
        Lax535992.LeastFixedPoint.Derives (A := I.Map A) rules q → B.mergeAssign σ q.1 q.2 := by
      intro q hq
      refine lfpAssign_least_of_closed (A := I.Map A) (ρ := B.mergeAssign σ)
        (fun c hc a ha v hg hb => ?_) hq
      have hsplit := tagVal_split I v
      have hpull : (c.pull I (fun j => (v j).1)).Holds (B.pullAssign (B.mergeAssign σ))
          (fun m => (v (finProdFinEquiv.symm m).1).2 (finProdFinEquiv.symm m).2) := by
        rw [B.pullAssign_mergeAssign σ, hσ]
        exact lfpAssign_rule (HornProgram.pull_mem I hc _)
          (by rw [HornClause.pull, ha]; rfl) _
      rw [HornClause.pull_holds I c _ (B.mergeAssign σ) _, hsplit] at hpull
      have hhead := hpull ⟨hg, hb⟩
      unfold Lax535992.HornFragment.HornClause.HeadHolds at hhead
      rwa [ha, Option.elim_some] at hhead
    have key := congrFun (congrFun (B.pullAssign_mergeAssign σ) p) x
    exact key ▸ hsub ⟨p.1, fun kk => (p.2 kk, fun j => x (finProdFinEquiv (kk, j)))⟩ h

end Pull

/-! ### Definitions in FO(LFP) -/

namespace LFPDef

end LFPDef

/-! ### SO-Horn definitions are FO(LFP) definitions

A Horn program splits into its *rules* (the clauses with a head), which define
the fixed point, and its *goal clauses* (those without), which merely say that
the fixed point avoids certain configurations – a first-order statement about
it, and so exactly what an output formula can express. -/

section OfHorn

section Realize

end Realize

end OfHorn

/-! ### Closure under reductions -/

section Closure

end Closure

end Lax794877Proofs.DescriptiveComplexity


