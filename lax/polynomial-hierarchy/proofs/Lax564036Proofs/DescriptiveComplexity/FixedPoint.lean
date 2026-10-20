/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Set.Card
import Lax564036Proofs.DescriptiveComplexity.Iterate
import Lax564036Proofs.DescriptiveComplexity.SecondOrderHorn
import Lax564036Proofs.DescriptiveComplexity.SecondOrderHornPull
import Lax564036Proofs.DescriptiveComplexity.Padding
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
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

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax564036Proofs.DescriptiveComplexity.LFPDef
end Lax564036Proofs.DescriptiveComplexity.LFPDef

namespace Lax564036Proofs.DescriptiveComplexity.LFPDefinable
end Lax564036Proofs.DescriptiveComplexity.LFPDefinable

namespace Lax564036Proofs.DescriptiveComplexity.SigmaSOHornDefinable
end Lax564036Proofs.DescriptiveComplexity.SigmaSOHornDefinable

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornClause HornProgram SigmaSOHornDefinable)
end Lax564036Proofs.DescriptiveComplexity

namespace Lax564036Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (Derives LFPDef LFPDefinable lfpAssign)
end Lax564036Proofs.DescriptiveComplexity

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

namespace Lax564036Proofs.DescriptiveComplexity

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

/-- The least fixed point is contained in every assignment satisfying the
rules. -/
theorem lfpAssign_least {rules : List (Lax535992.HornFragment.HornClause Lg B k)}
    {ρ : B.Assignment A} (hρ : ∀ v : Fin k → A, ∀ c ∈ rules, c.Holds ρ v)
    {p : Σ i : B.ι, Fin (B.arity i) → A} (hp : Lax535992.LeastFixedPoint.Derives rules p) : ρ p.1 p.2 := by
  refine lfpAssign_least_of_closed (fun c hc a ha v hg hb => ?_) hp
  have := hρ v c hc ⟨hg, hb⟩
  rwa [Lax535992.HornFragment.HornClause.HeadHolds, ha, Option.elim_some] at this

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

/-- One application of the rules to a set of atoms. -/
def stepDerives (rules : List (Lax535992.HornFragment.HornClause Lg B k)) (S : BAtom B A → Prop) :
    BAtom B A → Prop :=
  fun q => ∃ c ∈ rules, ∃ a : Lax485149.SecondOrderAtoms.SOAtom B k, c.head = some a ∧ ∃ v : Fin k → A,
    q = ⟨a.idx, fun j => v (a.args j)⟩ ∧ c.guard.Realize v ∧
      ∀ b ∈ c.body, S ⟨b.idx, fun j => v (b.args j)⟩

/-- The stages of the derivation: what is derivable in at most `n` rounds. -/
def derivesIn (rules : List (Lax535992.HornFragment.HornClause Lg B k)) : ℕ → BAtom B A → Prop
  | 0 => fun _ => False
  | n + 1 => fun q => derivesIn rules n q ∨ stepDerives rules (derivesIn rules n) q

theorem derivesIn_succ {rules : List (Lax535992.HornFragment.HornClause Lg B k)} {n : ℕ} {q : BAtom B A}
    (h : derivesIn rules n q) : derivesIn rules (n + 1) q := Or.inl h

theorem derivesIn_le {rules : List (Lax535992.HornFragment.HornClause Lg B k)} {m n : ℕ} (hmn : m ≤ n)
    {q : BAtom B A} (h : derivesIn rules m q) : derivesIn rules n q := by
  induction n with
  | zero => rwa [Nat.le_zero.mp hmn] at h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
    · exact derivesIn_succ (ih (Nat.lt_succ_iff.mp hlt))
    · rwa [heq] at h

/-- Finitely many derivable atoms share a stage. -/
private theorem exists_common_stage {rules : List (Lax535992.HornFragment.HornClause Lg B k)}
    (l : List (BAtom B A)) (h : ∀ q ∈ l, ∃ n, derivesIn rules n q) :
    ∃ N, ∀ q ∈ l, derivesIn rules N q := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons q l ih =>
    obtain ⟨n, hn⟩ := h q (List.mem_cons_self ..)
    obtain ⟨N, hN⟩ := ih fun r hr => h r (List.mem_cons_of_mem _ hr)
    refine ⟨max n N, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hr'
    · exact derivesIn_le (le_max_left _ _) hn
    · exact derivesIn_le (le_max_right _ _) (hN r hr')

/-- The stages exhaust the least fixed point. -/
theorem derives_iff_derivesIn {rules : List (Lax535992.HornFragment.HornClause Lg B k)} {q : BAtom B A} :
    Lax535992.LeastFixedPoint.Derives rules q ↔ ∃ n, derivesIn rules n q := by
  constructor
  · intro h
    induction h with
    | @rule c hc a ha v hg hb ih =>
      obtain ⟨N, hN⟩ :=
        exists_common_stage (rules := rules)
          (c.body.map fun b : Lax485149.SecondOrderAtoms.SOAtom B k => (⟨b.idx, fun j => v (b.args j)⟩ : BAtom B A))
          (fun q hq => by
            obtain ⟨b, hbmem, rfl⟩ := List.mem_map.mp hq
            exact ih b hbmem)
      exact ⟨N + 1, Or.inr ⟨c, hc, a, ha, v, rfl, hg,
        fun b hbmem => hN _ (List.mem_map_of_mem hbmem)⟩⟩
  · rintro ⟨n, hn⟩
    induction n generalizing q with
    | zero => exact hn.elim
    | succ n ih =>
      rcases hn with h | ⟨c, hc, a, ha, v, rfl, hg, hb⟩
      · exact ih h
      · exact Lax535992.LeastFixedPoint.Derives.rule hc ha hg fun b hbmem => ih (hb b hbmem)

/-! #### Depth, and the certificate -/

/-! #### Stabilization: the stages close within `Nat.card` many rounds

On a finite structure the stages are an increasing chain of subsets of the
finitely many atoms, so they stabilize by the time the atom count is reached
(`DescriptiveComplexity.exists_succ_eq_of_monotone_subset`, the one chain
pigeonhole of the library, in `DescriptiveComplexity.Iterate`) – after that many
rounds, `DescriptiveComplexity.derivesIn` *is* the least fixed point. This is
what lets a stage indexed by a large enough tuple stand in for the fixed point
itself in `DescriptiveComplexity.FixedPointHorn`. -/

private theorem stepDerives_congr {rules : List (Lax535992.HornFragment.HornClause Lg B k)}
    {S S' : BAtom B A → Prop} (h : ∀ q, S q ↔ S' q) (q : BAtom B A) :
    stepDerives rules S q ↔ stepDerives rules S' q := by
  unfold stepDerives
  exact exists_congr fun c => and_congr Iff.rfl <| exists_congr fun a =>
    and_congr Iff.rfl <| exists_congr fun v => and_congr Iff.rfl <| and_congr Iff.rfl <|
      forall_congr' fun b => forall_congr' fun _ => h _

private theorem derivesIn_of_stab {rules : List (Lax535992.HornFragment.HornClause Lg B k)} {N : ℕ}
    (hN : ∀ q : BAtom B A, derivesIn rules N q ↔ derivesIn rules (N + 1) q) :
    ∀ (s : ℕ) (q : BAtom B A), N ≤ s → (derivesIn rules s q ↔ derivesIn rules N q) := by
  intro s
  induction s with
  | zero =>
    intro q hq
    rw [Nat.le_zero.mp hq]
  | succ s ih =>
    intro q hs
    rcases Nat.lt_or_ge N (s + 1) with h | h
    · have hNs : N ≤ s := by omega
      constructor
      · rintro (h1 | h2)
        · exact (ih q hNs).mp h1
        · exact (hN q).mpr (Or.inr ((stepDerives_congr (fun r => ih r hNs) q).mp h2))
      · intro h1
        exact Or.inl ((ih q hNs).mpr h1)
    · have : N = s + 1 := le_antisymm hs h
      rw [this]

private theorem exists_stab [Finite A] (rules : List (Lax535992.HornFragment.HornClause Lg B k)) :
    ∃ N ≤ Nat.card (BAtom B A),
      ∀ q : BAtom B A, derivesIn rules N q ↔ derivesIn rules (N + 1) q := by
  obtain ⟨N, hN, heq⟩ := exists_succ_eq_of_monotone_subset
    (c := fun n => {q : BAtom B A | derivesIn rules n q}) fun n q hq => derivesIn_succ hq
  exact ⟨N, hN, fun q =>
    ⟨fun hq => (Set.ext_iff.mp heq q).mpr hq, fun hq => (Set.ext_iff.mp heq q).mp hq⟩⟩

/-- **The stages stabilize at the atom count**: after `Nat.card (BAtom B A)`
many rounds, being derivable within that many rounds is being derivable. -/
theorem derivesIn_iff_derives_of_card_le [Finite A] {rules : List (Lax535992.HornFragment.HornClause Lg B k)}
    {r : ℕ} (hr : Nat.card (BAtom B A) ≤ r) {q : BAtom B A} :
    derivesIn rules r q ↔ Lax535992.LeastFixedPoint.Derives rules q := by
  obtain ⟨N, hN, hstab⟩ := exists_stab (A := A) rules
  constructor
  · exact fun h => derives_iff_derivesIn.mpr ⟨r, h⟩
  · intro h
    obtain ⟨n, hn⟩ := derives_iff_derivesIn.mp h
    rcases Nat.lt_or_ge r n with hnr | hnr
    · exact (derivesIn_of_stab hstab r q (by omega)).mpr
        ((derivesIn_of_stab hstab n q (by omega)).mp hn)
    · exact derivesIn_le hnr hn

end Stages

/-! ### The fixed point transports along isomorphisms -/

section Map

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

end Pull

/-! ### Definitions in FO(LFP) -/

namespace LFPDef

variable {L : Language.{0, 0}} (d : Lax535992.LeastFixedPoint.LFPDef L)

/-- Negating the output complements the defined property: FO(LFP) is closed
under complement *by construction*, being a logic rather than a fragment. -/
def not : Lax535992.LeastFixedPoint.LFPDef L :=
  { B := d.B, k := d.k, rules := d.rules, out := ∼d.out }

end LFPDef

end Lax564036Proofs.DescriptiveComplexity

namespace Lax535992.LeastFixedPoint.LFPDef

export Lax564036Proofs.DescriptiveComplexity.LFPDef (not)

end Lax535992.LeastFixedPoint.LFPDef

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace LFPDef

variable {L : Language.{0, 0}} (d : Lax535992.LeastFixedPoint.LFPDef L)

theorem holds_not (A : Type) [L.Structure A] [LinearOrder A] :
    d.not.Holds A ↔ ¬d.Holds A :=
  Iff.rfl

end LFPDef

end Lax564036Proofs.DescriptiveComplexity

namespace Lax535992.LeastFixedPoint.LFPDef

export Lax564036Proofs.DescriptiveComplexity.LFPDef (holds_not)

end Lax535992.LeastFixedPoint.LFPDef

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace LFPDef

variable {L : Language.{0, 0}} (d : Lax535992.LeastFixedPoint.LFPDef L)

end LFPDef

/-- **FO(LFP) definability is closed under complement.** This is the one line
that the Horn fragment cannot supply, and the reason to have the logic at all:
negate the output formula. -/
theorem LFPDefinable.compl {L : Language.{0, 0}} [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
    (h : Lax535992.LeastFixedPoint.LFPDefinable P) : Lax535992.LeastFixedPoint.LFPDefinable Pᶜ := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.not, ?_⟩
  intro A _ _ _ _
  exact (not_congr (hd A)).trans (d.holds_not A).symm

end Lax564036Proofs.DescriptiveComplexity

namespace Lax535992.LeastFixedPoint.LFPDefinable

export Lax564036Proofs.DescriptiveComplexity.LFPDefinable (compl)

end Lax535992.LeastFixedPoint.LFPDefinable

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### SO-Horn definitions are FO(LFP) definitions

A Horn program splits into its *rules* (the clauses with a head), which define
the fixed point, and its *goal clauses* (those without), which merely say that
the fixed point avoids certain configurations – a first-order statement about
it, and so exactly what an output formula can express. -/

section OfHorn

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

/-- The symbol of a relation variable of the block. -/
abbrev varSym (B : Lax904597.SecondOrder.SOBlock) (i : B.ι) : B.lang.Relations (B.arity i) := ⟨i, rfl⟩

/-- The symbol of a relation variable, in the expanded vocabulary. -/
abbrev varOutSym (L : Language.{0, 0}) (B : Lax904597.SecondOrder.SOBlock) (i : B.ι) :
    ((L.sum Language.order).sum B.lang).Relations (B.arity i) :=
  Sum.inr (varSym B i)

/-- A second-order atom, as a first-order atom over the expanded
vocabulary. -/
noncomputable def atomF (a : Lax485149.SecondOrderAtoms.SOAtom B k) :
    ((L.sum Language.order).sum B.lang).Formula (Empty ⊕ Fin k) :=
  Relations.formula (varOutSym L B a.idx) fun j => Term.var (Sum.inr (a.args j))

/-- A guard, transported to the expanded vocabulary. -/
noncomputable def guardOutF (φ : (L.sum Language.order).Formula (Fin k)) :
    ((L.sum Language.order).sum B.lang).Formula (Empty ⊕ Fin k) :=
  (LHom.sumInl.onFormula φ).relabel Sum.inr

/-- A goal clause, as the first-order statement that it never fires. -/
noncomputable def goalOutF (c : Lax535992.HornFragment.HornClause (L.sum Language.order) B k) :
    ((L.sum Language.order).sum B.lang).Sentence :=
  (show ((L.sum Language.order).sum B.lang).Formula (Empty ⊕ Fin k) from
    ∼(guardOutF c.guard ⊓ listInf (c.body.map atomF))).iAlls (Fin k)

/-- The output formula of the translation: no goal clause of the program ever
fires at the fixed point. -/
noncomputable def hornOutF (prog : Lax535992.HornFragment.HornProgram (L.sum Language.order) B k) :
    ((L.sum Language.order).sum B.lang).Sentence :=
  listInf ((prog.filter fun c => c.head.isNone).map goalOutF)

section Realize

variable {A : Type} [L.Structure A] [LinearOrder A] (ρ : B.Assignment A)

theorem realize_atomF (a : Lax485149.SecondOrderAtoms.SOAtom B k) (v : (Empty ⊕ Fin k) → A) :
    (@Formula.Realize ((L.sum Language.order).sum B.lang) A
        (@sumStructure _ _ A _ (B.structure ρ)) _ (atomF a) v) ↔
      a.Holds ρ fun j => v (Sum.inr j) := by
  let := B.structure ρ
  rw [atomF, Formula.realize_rel]
  exact Iff.rfl

theorem realize_guardOutF (φ : (L.sum Language.order).Formula (Fin k))
    (v : (Empty ⊕ Fin k) → A) :
    (@Formula.Realize ((L.sum Language.order).sum B.lang) A
        (@sumStructure _ _ A _ (B.structure ρ)) _ (guardOutF φ) v) ↔
      φ.Realize fun j => v (Sum.inr j) := by
  let := B.structure ρ
  rw [guardOutF, Formula.realize_relabel, LHom.realize_onFormula]
  rfl

theorem realize_goalOutF (c : Lax535992.HornFragment.HornClause (L.sum Language.order) B k) :
    (@Sentence.Realize ((L.sum Language.order).sum B.lang) A
        (@sumStructure _ _ A _ (B.structure ρ)) (goalOutF c)) ↔
      ∀ v : Fin k → A, ¬(c.guard.Realize v ∧ ∀ b ∈ c.body, b.Holds ρ v) := by
  let := B.structure ρ
  rw [goalOutF]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_not,
    Formula.realize_inf, realize_guardOutF ρ, realize_listInf]
  refine ⟨fun h v hv => h (fun j => v j) ⟨hv.1, fun ψ hψ => ?_⟩,
    fun h i hi => h (fun j => i j) ⟨hi.1, fun b hb => ?_⟩⟩
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hψ
    exact (realize_atomF ρ b _).mpr (hv.2 b hb)
  · exact (realize_atomF ρ b _).mp (hi.2 _ (List.mem_map_of_mem hb))

theorem realize_hornOutF (prog : Lax535992.HornFragment.HornProgram (L.sum Language.order) B k) :
    (@Sentence.Realize ((L.sum Language.order).sum B.lang) A
        (@sumStructure _ _ A _ (B.structure ρ)) (hornOutF prog)) ↔
      ∀ c ∈ prog, c.head = none →
        ∀ v : Fin k → A, ¬(c.guard.Realize v ∧ ∀ b ∈ c.body, b.Holds ρ v) := by
  let := B.structure ρ
  rw [hornOutF]
  simp only [Sentence.Realize, realize_listInf]
  constructor
  · intro h c hc hnone
    exact (realize_goalOutF ρ c).mp
      (h _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hc, by rw [hnone]; rfl⟩)))
  · intro h ψ hψ
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hψ
    obtain ⟨hcp, hnone⟩ := List.mem_filter.mp hc
    exact (realize_goalOutF ρ c).mpr (h c hcp (Option.isNone_iff_eq_none.mp hnone))

end Realize

/-- **Every SO-Horn definition is an FO(LFP) definition**: keep the rules,
and turn the goal clauses into the output formula. -/
theorem SigmaSOHornDefinable.lfpDefinable [L.IsRelational] {P : Lax904597.Problems.DecisionProblem L}
    (h : Lax535992.HornFragment.SigmaSOHornDefinable P) : Lax535992.LeastFixedPoint.LFPDefinable P := by
  obtain ⟨B, k, prog, hprog⟩ := h
  refine ⟨⟨B, k, prog, hornOutF prog⟩, ?_⟩
  intro A _ _ _ _
  refine (hprog A).trans ⟨?_, ?_⟩
  · rintro ⟨ρ, hρ⟩
    refine (realize_hornOutF (Lax535992.LeastFixedPoint.lfpAssign prog) prog).mpr fun c hc hnone v ⟨hg, hb⟩ => ?_
    have hsub : ∀ b : Lax485149.SecondOrderAtoms.SOAtom B k, b.Holds (Lax535992.LeastFixedPoint.lfpAssign prog) v → b.Holds ρ v := fun b hbv =>
      lfpAssign_least (p := ⟨b.idx, fun j => v (b.args j)⟩) hρ hbv
    have := hρ v c hc ⟨hg, fun b hbmem => hsub b (hb b hbmem)⟩
    rw [Lax535992.HornFragment.HornClause.HeadHolds, hnone, Option.elim_none] at this
    exact this
  · intro hout
    refine ⟨Lax535992.LeastFixedPoint.lfpAssign prog, fun v c hc => ?_⟩
    cases hh : c.head with
    | some a => exact lfpAssign_rule hc hh v
    | none =>
      intro hpre
      exact absurd hpre ((realize_hornOutF (Lax535992.LeastFixedPoint.lfpAssign prog) prog).mp hout c hc hh v)

end OfHorn

end Lax564036Proofs.DescriptiveComplexity

namespace Lax535992.HornFragment.SigmaSOHornDefinable

export Lax564036Proofs.DescriptiveComplexity.SigmaSOHornDefinable (lfpDefinable)

end Lax535992.HornFragment.SigmaSOHornDefinable

namespace Lax564036Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section OfHorn

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

end OfHorn

/-! ### Closure under reductions -/

section Closure

end Closure

end Lax564036Proofs.DescriptiveComplexity


