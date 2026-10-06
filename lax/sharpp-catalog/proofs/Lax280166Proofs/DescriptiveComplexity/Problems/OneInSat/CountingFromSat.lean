/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.OneInSat.Counting
import Lax280166Proofs.DescriptiveComplexity.Problems.OneInSat.ExactlyOne
import Lax280166Proofs.DescriptiveComplexity.Problems.ThreeSat.CountingFromSat
import Lax280166Proofs.DescriptiveComplexity.Counting.Subtractive
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

namespace Lax280166.CountingSatVariants
end Lax280166.CountingSatVariants

namespace Lax366625.CountingSat
end Lax366625.CountingSat

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc

namespace Lax799700.OneInSat
end Lax799700.OneInSat

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingSatVariants (OneInModel)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.OneInSat (OneInProper)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingSat (SatModel SatOccurs)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

namespace Lax280166Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (IsCl LitTrue OccIn)
end Lax280166Proofs.DescriptiveComplexity.SatOcc

/-!
# #SAT reduces parsimoniously to #1-in-SAT

The reduction of 3SAT to 1-in-SAT in
`DescriptiveComplexity.Problems.OneInSat.Reduction` uses the classical gadget, which
gives some satisfying assignments two extensions: it preserves satisfiability,
not the number of solutions. This file reduces #SAT to #1-in-SAT directly and
parsimoniously (`DescriptiveComplexity.sharpSat_ordered_parsimonious_sharpOneInSat`),
so #1-in-SAT is parsimoniously `#P`-complete
(`DescriptiveComplexity.sharpOneInSat_sharpP_parsimoniousComplete`).

As in `DescriptiveComplexity.Problems.ThreeSat.CountingFromSat`, each occurrence
`(x, s)` of a clause `c` has a prefix variable `z`, the truth of the
disjunction of the occurrences of `c` up to it
(`DescriptiveComplexity.OccurrencePrefix`). What changes is how `z ↔ z' ∨ ℓ` is said
with exactly-one clauses, `z'` being the prefix variable of the preceding
occurrence and `ℓ` the literal: three more variables name the cases
`z' ∧ ℓ`, `z' ∧ ¬ℓ` and `¬z' ∧ ℓ`, and three clauses,

* `{¬z', g₁₁, g₁₀}`, `{¬ℓ, g₁₁, g₀₁}` and `{¬z, g₁₁, g₁₀, g₀₁}`,

each with exactly one true literal, force them and `z`. The first occurrence
of a clause has the clause `{¬z, ℓ}`, and the last one the unit clause `{z}`.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

namespace SharpSatToOneIn

open Language Structure SatOcc

open SharpSatToThreeSat (OwnVar Same Pred ownVarF sameF predF ownVar_eq same_eq eta2)

/-- The three clauses of the gate of an occurrence. -/
inductive GK : Type
  /-- `{¬z', g₁₁, g₁₀}`. -/
  | a
  /-- `{¬ℓ, g₁₁, g₀₁}`. -/
  | b
  /-- `{¬z, g₁₁, g₁₀, g₀₁}`. -/
  | c
  deriving DecidableEq

instance : Fintype GK := ⟨{GK.a, GK.b, GK.c}, fun x => by cases x <;> decide⟩

/-- The three case variables of the gate of an occurrence. -/
inductive GI : Type
  /-- `z' ∧ ℓ`. -/
  | tt
  /-- `z' ∧ ¬ℓ`. -/
  | tf
  /-- `¬z' ∧ ℓ`. -/
  | ft
  deriving DecidableEq

instance : Fintype GI := ⟨{GI.tt, GI.tf, GI.ft}, fun x => by cases x <;> decide⟩

/-- Which case variables a gate clause contains. -/
def gateIn : GK → GI → Bool
  | .a, .tt => true
  | .a, .tf => true
  | .b, .tt => true
  | .b, .ft => true
  | .c, _ => true
  | _, _ => false

/-- Tags of the interpretation. -/
inductive OTag : Type
  /-- `(.var, (x, x))` is the copy of the propositional variable `x`. -/
  | var
  /-- `(.pre s, (c, x))` is the prefix variable of the occurrence `(x, s)` of
  the clause `c`. -/
  | pre (s : Bool)
  /-- A case variable of the gate of an occurrence. -/
  | g (i : GI) (s : Bool)
  /-- A clause of the gate of an occurrence that has a predecessor. -/
  | gk (k : GK) (s : Bool)
  /-- The clause `{¬z, ℓ}` of the first occurrence of a clause. -/
  | kd (s : Bool)
  /-- The unit clause `{z}` of the last occurrence of a clause. -/
  | top (s : Bool)
  /-- `(.empty, (c, c))` is the copy of the empty clause `c`. -/
  | empty
  deriving DecidableEq, Fintype

instance : Nonempty OTag := ⟨OTag.var⟩

/-- Defining formula for `satIsClause`. -/
noncomputable def isClauseF : OTag → satOrd.Formula (Fin 1 × Fin 2)
  | .gk _ s => chainedF s (0, 0) (0, 1)
  | .kd s => minOccF s (0, 0) (0, 1)
  | .top s => maxOccF s (0, 0) (0, 1)
  | .empty => eqF (0, 0) (0, 1) ⊓ emptyClF (0, 0)
  | _ => ⊥

/-- Defining formula for `satPosIn`. -/
noncomputable def posInF : OTag → OTag → satOrd.Formula (Fin 2 × Fin 2)
  | .gk k s, .g i t =>
      if gateIn k i = true ∧ t = s then sameF ⊓ chainedF s (0, 0) (0, 1) else ⊥
  | .gk k s, .var => if k = .b ∧ s = false then ownVarF ⊓ chainedF s (0, 0) (0, 1) else ⊥
  | .kd s, .var => if s = true then ownVarF ⊓ minOccF s (0, 0) (0, 1) else ⊥
  | .top s, .pre t => if t = s then sameF ⊓ maxOccF s (0, 0) (0, 1) else ⊥
  | _, _ => ⊥

/-- Defining formula for `satNegIn`. -/
noncomputable def negInF : OTag → OTag → satOrd.Formula (Fin 2 × Fin 2)
  | .gk k s, .pre t =>
      if k = .a then predF t s
      else if k = .c ∧ t = s then sameF ⊓ chainedF s (0, 0) (0, 1) else ⊥
  | .gk k s, .var => if k = .b ∧ s = true then ownVarF ⊓ chainedF s (0, 0) (0, 1) else ⊥
  | .kd s, .var => if s = false then ownVarF ⊓ minOccF s (0, 0) (0, 1) else ⊥
  | .kd s, .pre t => if t = s then sameF ⊓ minOccF s (0, 0) (0, 1) else ⊥
  | _, _ => ⊥

/-- The parsimonious interpretation of 1-in-SAT instances in ordered CNF
instances. -/
noncomputable def interp : Lax904597.Interpretations.FOInterpretation satOrd Lax904597.Sat.sat OTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun t => isClauseF (t 0)
    | _, .posIn => fun t => posInF (t 0) (t 1)
    | _, .negIn => fun t => negInF (t 0) (t 1)

/-! ### Characterization of the interpreted relations -/

section Characterizations

variable {A : Type} [instS : Lax904597.Sat.sat.Structure A] [instO : LinearOrder A]

/-- The semantic content of `isClauseF`. -/
def ClauseSem : OTag → (Fin 2 → A) → Prop
  | .gk _ s, w => Chained (w 0) (w 1) s
  | .kd s, w => MinOcc (w 0) (w 1) s
  | .top s, w => MaxOcc (w 0) (w 1) s
  | .empty, w => w 0 = w 1 ∧ EmptyCl (w 0)
  | _, _ => False

/-- The semantic content of `posInF`. -/
def PosSem : OTag → OTag → (Fin 2 → A) → (Fin 2 → A) → Prop
  | .gk k s, .g i t, w₁, w₂ =>
      (gateIn k i = true ∧ t = s) ∧ Same w₁ w₂ ∧ Chained (w₁ 0) (w₁ 1) s
  | .gk k s, .var, w₁, w₂ => (k = .b ∧ s = false) ∧ OwnVar w₁ w₂ ∧ Chained (w₁ 0) (w₁ 1) s
  | .kd s, .var, w₁, w₂ => s = true ∧ OwnVar w₁ w₂ ∧ MinOcc (w₁ 0) (w₁ 1) s
  | .top s, .pre t, w₁, w₂ => t = s ∧ Same w₁ w₂ ∧ MaxOcc (w₁ 0) (w₁ 1) s
  | _, _, _, _ => False

/-- The semantic content of `negInF`. -/
def NegSem : OTag → OTag → (Fin 2 → A) → (Fin 2 → A) → Prop
  | .gk k s, .pre t, w₁, w₂ =>
      (k = .a ∧ Pred t s w₁ w₂) ∨
        ((k = .c ∧ t = s) ∧ Same w₁ w₂ ∧ Chained (w₁ 0) (w₁ 1) s)
  | .gk k s, .var, w₁, w₂ => (k = .b ∧ s = true) ∧ OwnVar w₁ w₂ ∧ Chained (w₁ 0) (w₁ 1) s
  | .kd s, .var, w₁, w₂ => s = false ∧ OwnVar w₁ w₂ ∧ MinOcc (w₁ 0) (w₁ 1) s
  | .kd s, .pre t, w₁, w₂ => t = s ∧ Same w₁ w₂ ∧ MinOcc (w₁ 0) (w₁ 1) s
  | _, _, _, _ => False

theorem isClause_iff (t : OTag) (w : Fin 2 → A) :
    RelMap (M := interp.Map A) Lax904597.Sat.satIsClause ![(t, w)] ↔ ClauseSem t w := by
  rw [FOInterpretation.relMap_map]
  cases t <;> simp [interp, isClauseF, ClauseSem]

theorem posIn_iff (t₁ t₂ : OTag) (w₁ w₂ : Fin 2 → A) :
    RelMap (M := interp.Map A) Lax904597.Sat.satPosIn ![(t₁, w₁), (t₂, w₂)] ↔ PosSem t₁ t₂ w₁ w₂ := by
  rw [FOInterpretation.relMap_map]
  cases t₁ <;> cases t₂ <;> try exact Iff.rfl
  case gk.g k s i t =>
    cases k <;> cases i <;> cases s <;> cases t <;>
      simp [interp, posInF, PosSem, gateIn, sameF, Same, and_assoc]
  case gk.var k s =>
    cases k <;> cases s <;> simp [interp, posInF, PosSem, ownVarF, OwnVar, and_assoc]
  case kd.var s =>
    cases s <;> simp [interp, posInF, PosSem, ownVarF, OwnVar, and_assoc]
  case top.pre s t =>
    cases s <;> cases t <;> simp [interp, posInF, PosSem, sameF, Same, and_assoc]

theorem negIn_iff (t₁ t₂ : OTag) (w₁ w₂ : Fin 2 → A) :
    RelMap (M := interp.Map A) Lax904597.Sat.satNegIn ![(t₁, w₁), (t₂, w₂)] ↔ NegSem t₁ t₂ w₁ w₂ := by
  rw [FOInterpretation.relMap_map]
  cases t₁ <;> cases t₂ <;> try exact Iff.rfl
  case gk.pre k s t =>
    cases k <;> cases s <;> cases t <;>
      simp [interp, negInF, NegSem, predF, Pred, sameF, Same, and_assoc]
  case gk.var k s =>
    cases k <;> cases s <;> simp [interp, negInF, NegSem, ownVarF, OwnVar, and_assoc]
  case kd.var s =>
    cases s <;> simp [interp, negInF, NegSem, ownVarF, OwnVar, and_assoc]
  case kd.pre s t =>
    cases s <;> cases t <;> simp [interp, negInF, NegSem, sameF, Same, and_assoc]

end Characterizations

/-! ### The literals of each clause -/

section Literals

variable {A : Type} [instS : Lax904597.Sat.sat.Structure A] [instO : LinearOrder A]

/-- The literals of the interpreted instance, with their sign. -/
def LitSem : Bool → OTag → OTag → (Fin 2 → A) → (Fin 2 → A) → Prop
  | true => PosSem
  | false => NegSem

theorem occIn_map_iff (t te : OTag) (w we : Fin 2 → A) (sg : Bool) :
    Lax799700.Common.SatOcc.OccIn (A := interp.Map A) (t, w) (te, we) sg ↔ ClauseSem t w ∧ LitSem sg t te w we := by
  cases sg
  · exact and_congr (isClause_iff t w) (negIn_iff t te w we)
  · exact and_congr (isClause_iff t w) (posIn_iff t te w we)

/-- The copy of the variable `x`. -/
def varP (x : A) : interp.Map A := (OTag.var, fun _ => x)

/-- The prefix variable of the occurrence `(x, s)` of `c`. -/
def preP (s : Bool) (c x : A) : interp.Map A := (OTag.pre s, ![c, x])

/-- A case variable of the gate of the occurrence `(x, s)` of `c`. -/
def gP (i : GI) (s : Bool) (c x : A) : interp.Map A := (OTag.g i s, ![c, x])

omit instS instO in
theorem pair_eq {t : OTag} {we : Fin 2 → A} {c x : A} (h0 : we 0 = c) (h1 : we 1 = x) :
    ((t, we) : interp.Map A) = (t, ![c, x]) := by
  have : we = ![c, x] := by
    funext k
    fin_cases k
    · exact h0
    · exact h1
  rw [this]

omit instS instO in
theorem var_eq {w we : Fin 2 → A} (h : OwnVar w we) :
    ((OTag.var, we) : interp.Map A) = varP (w 1) := by
  rw [ownVar_eq h]
  rfl

/-- The literal of the unit clause of a last occurrence. -/
theorem occIn_top {c x : A} {s : Bool} (hmax : MaxOcc c x s) (e : interp.Map A) (sg : Bool) :
    Lax799700.Common.SatOcc.OccIn (A := interp.Map A) (OTag.top s, ![c, x]) e sg ↔ e = preP s c x ∧ sg = true := by
  constructor
  · obtain ⟨te, we⟩ := e
    rw [occIn_map_iff]
    rintro ⟨-, hl⟩
    cases sg <;> cases te <;> try exact hl.elim
    case true.pre t =>
      obtain ⟨rfl, hsame, -⟩ := hl
      exact ⟨pair_eq hsame.1.symm hsame.2.symm, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact (occIn_map_iff _ _ _ _ _).mpr ⟨hmax, rfl, ⟨rfl, rfl⟩, hmax⟩

/-- The literals of the clause of a first occurrence. -/
theorem occIn_kd {c x : A} {s : Bool} (hmin : MinOcc c x s) (e : interp.Map A) (sg : Bool) :
    Lax799700.Common.SatOcc.OccIn (A := interp.Map A) (OTag.kd s, ![c, x]) e sg ↔
      (e = preP s c x ∧ sg = false) ∨ (e = varP x ∧ sg = s) := by
  constructor
  · obtain ⟨te, we⟩ := e
    rw [occIn_map_iff]
    rintro ⟨-, hl⟩
    cases sg <;> cases te <;> try exact hl.elim
    case false.var =>
      obtain ⟨rfl, hown, -⟩ := hl
      exact Or.inr ⟨var_eq hown, rfl⟩
    case false.pre t =>
      obtain ⟨rfl, hsame, -⟩ := hl
      exact Or.inl ⟨pair_eq hsame.1.symm hsame.2.symm, rfl⟩
    case true.var =>
      obtain ⟨rfl, hown, -⟩ := hl
      exact Or.inr ⟨var_eq hown, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact (occIn_map_iff _ _ _ _ _).mpr ⟨hmin, rfl, ⟨rfl, rfl⟩, hmin⟩
    · cases sg
      · exact (occIn_map_iff _ _ _ _ _).mpr ⟨hmin, rfl, ⟨rfl, rfl⟩, hmin⟩
      · exact (occIn_map_iff _ _ _ _ _).mpr ⟨hmin, rfl, ⟨rfl, rfl⟩, hmin⟩

omit instO in
theorem chained_of_succOcc [LinearOrder A] {c y x : A} {t s : Bool}
    (h : SuccOcc c y t x s) : Chained c x s :=
  ⟨h.2.1, fun hmin => hmin.2 y t h.1 h.2.2.1⟩

/-- The literals of the first gate clause, `{¬z', g₁₁, g₁₀}`. -/
theorem occIn_ka {c y x : A} {t s : Bool} (hsucc : SuccOcc c y t x s) (e : interp.Map A)
    (sg : Bool) :
    Lax799700.Common.SatOcc.OccIn (A := interp.Map A) (OTag.gk .a s, ![c, x]) e sg ↔
      (e = preP t c y ∧ sg = false) ∨ (e = gP .tt s c x ∧ sg = true) ∨
        (e = gP .tf s c x ∧ sg = true) := by
  have hch := chained_of_succOcc hsucc
  constructor
  · obtain ⟨te, we⟩ := e
    rw [occIn_map_iff]
    rintro ⟨-, hl⟩
    cases sg <;> cases te <;> try exact hl.elim
    case false.var => exact absurd hl.1.1 (by decide)
    case false.pre t' =>
      rcases hl with ⟨-, hpred⟩ | ⟨⟨hk, -⟩, -⟩
      · obtain ⟨hy, rfl⟩ := succOcc_left_unique hsucc hpred.2
        exact Or.inl ⟨pair_eq hpred.1.symm hy.symm, rfl⟩
      · exact absurd hk (by decide)
    case true.var => exact absurd hl.1.1 (by decide)
    case true.g i t' =>
      obtain ⟨⟨hin, rfl⟩, hsame, -⟩ := hl
      cases i
      · exact Or.inr (Or.inl ⟨pair_eq hsame.1.symm hsame.2.symm, rfl⟩)
      · exact Or.inr (Or.inr ⟨pair_eq hsame.1.symm hsame.2.symm, rfl⟩)
      · exact absurd hin (by decide)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact (occIn_map_iff _ _ _ _ _).mpr ⟨hch, Or.inl ⟨rfl, rfl, hsucc⟩⟩
    · exact (occIn_map_iff _ _ _ _ _).mpr ⟨hch, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hch⟩
    · exact (occIn_map_iff _ _ _ _ _).mpr ⟨hch, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hch⟩

/-- The literals of the second gate clause, `{¬ℓ, g₁₁, g₀₁}`. -/
theorem occIn_kb {c x : A} {s : Bool} (hch : Chained c x s) (e : interp.Map A) (sg : Bool) :
    Lax799700.Common.SatOcc.OccIn (A := interp.Map A) (OTag.gk .b s, ![c, x]) e sg ↔
      (e = varP x ∧ sg = !s) ∨ (e = gP .tt s c x ∧ sg = true) ∨
        (e = gP .ft s c x ∧ sg = true) := by
  constructor
  · obtain ⟨te, we⟩ := e
    rw [occIn_map_iff]
    rintro ⟨-, hl⟩
    cases sg <;> cases te <;> try exact hl.elim
    case false.var =>
      obtain ⟨⟨-, rfl⟩, hown, -⟩ := hl
      exact Or.inl ⟨var_eq hown, rfl⟩
    case false.pre t' =>
      rcases hl with ⟨hk, -⟩ | ⟨⟨hk, -⟩, -⟩ <;> exact absurd hk (by decide)
    case true.var =>
      obtain ⟨⟨-, rfl⟩, hown, -⟩ := hl
      exact Or.inl ⟨var_eq hown, rfl⟩
    case true.g i t' =>
      obtain ⟨⟨hin, rfl⟩, hsame, -⟩ := hl
      cases i
      · exact Or.inr (Or.inl ⟨pair_eq hsame.1.symm hsame.2.symm, rfl⟩)
      · exact absurd hin (by decide)
      · exact Or.inr (Or.inr ⟨pair_eq hsame.1.symm hsame.2.symm, rfl⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · cases s
      · exact (occIn_map_iff _ _ _ _ _).mpr ⟨hch, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hch⟩
      · exact (occIn_map_iff _ _ _ _ _).mpr ⟨hch, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hch⟩
    · exact (occIn_map_iff _ _ _ _ _).mpr ⟨hch, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hch⟩
    · exact (occIn_map_iff _ _ _ _ _).mpr ⟨hch, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hch⟩

/-- The literals of the third gate clause, `{¬z, g₁₁, g₁₀, g₀₁}`. -/
theorem occIn_kc {c x : A} {s : Bool} (hch : Chained c x s) (e : interp.Map A) (sg : Bool) :
    Lax799700.Common.SatOcc.OccIn (A := interp.Map A) (OTag.gk .c s, ![c, x]) e sg ↔
      (e = preP s c x ∧ sg = false) ∨ (e = gP .tt s c x ∧ sg = true) ∨
        (e = gP .tf s c x ∧ sg = true) ∨ (e = gP .ft s c x ∧ sg = true) := by
  constructor
  · obtain ⟨te, we⟩ := e
    rw [occIn_map_iff]
    rintro ⟨-, hl⟩
    cases sg <;> cases te <;> try exact hl.elim
    case false.var => exact absurd hl.1.1 (by decide)
    case false.pre t' =>
      rcases hl with ⟨hk, -⟩ | ⟨⟨-, rfl⟩, hsame, -⟩
      · exact absurd hk (by decide)
      · exact Or.inl ⟨pair_eq hsame.1.symm hsame.2.symm, rfl⟩
    case true.var => exact absurd hl.1.1 (by decide)
    case true.g i t' =>
      obtain ⟨⟨-, rfl⟩, hsame, -⟩ := hl
      cases i
      · exact Or.inr (Or.inl ⟨pair_eq hsame.1.symm hsame.2.symm, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨pair_eq hsame.1.symm hsame.2.symm, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨pair_eq hsame.1.symm hsame.2.symm, rfl⟩))
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact (occIn_map_iff _ _ _ _ _).mpr ⟨hch, Or.inr ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hch⟩⟩
    · exact (occIn_map_iff _ _ _ _ _).mpr ⟨hch, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hch⟩
    · exact (occIn_map_iff _ _ _ _ _).mpr ⟨hch, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hch⟩
    · exact (occIn_map_iff _ _ _ _ _).mpr ⟨hch, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hch⟩

/-- The copy of an empty clause has no literal. -/
theorem not_occIn_empty {w : Fin 2 → A} (e : interp.Map A) (sg : Bool) :
    ¬Lax799700.Common.SatOcc.OccIn (A := interp.Map A) (OTag.empty, w) e sg := by
  obtain ⟨te, we⟩ := e
  rw [occIn_map_iff]
  rintro ⟨-, hl⟩
  cases sg <;> cases te <;> exact hl.elim

end Literals

/-! ### Exactly-one assignments, read as gate valuations -/

section Assignments

variable {A : Type} [instS : Lax904597.Sat.sat.Structure A] [instO : LinearOrder A]

/-- A **gate valuation** of the assignment `ν`: prefix values `Z` and case
values `G`, each forced by `ν` along the occurrences of every clause, with the
prefix value true at the last occurrence and no empty clause. -/
structure GateVal (ν : A → Prop) (Z : A → A → Bool → Prop)
    (G : GI → A → A → Bool → Prop) : Prop where
  /-- At a first occurrence the prefix value is the literal. -/
  first : ∀ c x s, MinOcc c x s → (Z c x s ↔ Lax799700.Common.SatOcc.LitTrue ν x s)
  /-- At an occurrence with a predecessor, the case values name the cases of
  the previous prefix value and the literal, and the prefix value is their
  disjunction. -/
  gate : ∀ c y t x s, SuccOcc c y t x s →
    (G .tt c x s ↔ Z c y t ∧ Lax799700.Common.SatOcc.LitTrue ν x s) ∧ (G .tf c x s ↔ Z c y t ∧ ¬Lax799700.Common.SatOcc.LitTrue ν x s) ∧
      (G .ft c x s ↔ ¬Z c y t ∧ Lax799700.Common.SatOcc.LitTrue ν x s) ∧ (Z c x s ↔ Z c y t ∨ Lax799700.Common.SatOcc.LitTrue ν x s)
  /-- The prefix value at the last occurrence of a clause is true. -/
  last : ∀ c x s, MaxOcc c x s → Z c x s
  /-- No clause is empty. -/
  nonempty : ∀ c : A, ¬EmptyCl c

/-- A gate valuation is in particular a prefix valuation. -/
theorem GateVal.prefixVal [Finite A] {ν : A → Prop} {Z : A → A → Bool → Prop}
    {G : GI → A → A → Bool → Prop} (h : GateVal ν Z G) : PrefixVal ν Z where
  step c x s hocc := by
    by_cases hmin : MinOcc c x s
    · rw [h.first c x s hmin]
      refine ⟨Or.inl, fun hor => hor.resolve_right ?_⟩
      rintro ⟨y, t, hsucc, -⟩
      exact hmin.2 y t hsucc.1 hsucc.2.2.1
    · obtain ⟨y, t, hsucc⟩ := exists_succOcc ⟨hocc, hmin⟩
      rw [(h.gate c y t x s hsucc).2.2.2, or_comm]
      refine or_congr_right ⟨fun hz => ⟨y, t, hsucc, hz⟩, ?_⟩
      rintro ⟨y', t', hsucc', hz⟩
      obtain ⟨rfl, rfl⟩ := succOcc_left_unique hsucc hsucc'
      exact hz
  last := h.last
  nonempty := h.nonempty

omit instS instO in
/-- The propositional content of a gate: the three exactly-one clauses
`{¬a, g₁₁, g₁₀}`, `{¬b, g₁₁, g₀₁}` and `{¬z, g₁₁, g₁₀, g₀₁}` say that the case
variables name the cases of `a` and `b`, and that `z` is `a ∨ b`. -/
theorem gate_prop (a b z g₁₁ g₁₀ g₀₁ : Prop) :
    (((¬a ∧ ¬g₁₁ ∧ ¬g₁₀) ∨ (¬¬a ∧ g₁₁ ∧ ¬g₁₀) ∨ (¬¬a ∧ ¬g₁₁ ∧ g₁₀)) ∧
      ((¬b ∧ ¬g₁₁ ∧ ¬g₀₁) ∨ (¬¬b ∧ g₁₁ ∧ ¬g₀₁) ∨ (¬¬b ∧ ¬g₁₁ ∧ g₀₁)) ∧
      ((¬z ∧ ¬g₁₁ ∧ ¬g₁₀ ∧ ¬g₀₁) ∨ (¬¬z ∧ g₁₁ ∧ ¬g₁₀ ∧ ¬g₀₁) ∨ (¬¬z ∧ ¬g₁₁ ∧ g₁₀ ∧ ¬g₀₁) ∨
        (¬¬z ∧ ¬g₁₁ ∧ ¬g₁₀ ∧ g₀₁))) ↔
      ((g₁₁ ↔ a ∧ b) ∧ (g₁₀ ↔ a ∧ ¬b) ∧ (g₀₁ ↔ ¬a ∧ b) ∧ (z ↔ a ∨ b)) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hz : z <;> by_cases h₁₁ : g₁₁ <;>
    by_cases h₁₀ : g₁₀ <;> by_cases h₀₁ : g₀₁ <;> simp [ha, hb, hz, h₁₁, h₁₀, h₀₁]

variable (μ : interp.Map A → Prop)

/-- The assignment read on the variable copies. -/
def varVal (x : A) : Prop := μ (varP x)

/-- The assignment read on the prefix variables. -/
def preVal (c x : A) (s : Bool) : Prop := μ (preP s c x)

/-- The assignment read on the case variables. -/
def gVal (i : GI) (c x : A) (s : Bool) : Prop := μ (gP i s c x)

variable {μ}

omit instS instO in
theorem ne_of_tag {t t' : OTag} {w w' : Fin 2 → A} (h : t ≠ t') :
    ((t, w) : interp.Map A) ≠ (t', w') := fun he => h (congrArg Prod.fst he)

/-- **Every clause of the interpreted instance has exactly one true literal
exactly when the assignment is a gate valuation**, read on the variable copies,
the prefix variables and the case variables. -/
theorem oneInProper_iff_gateVal [Finite A] :
    Lax799700.OneInSat.OneInProper μ ↔ GateVal (varVal μ) (preVal μ) (gVal μ) := by
  have hpre : ∀ c x s, (Lax799700.Common.SatOcc.LitTrue μ (preP s c x) false ↔ ¬preVal μ c x s) ∧
      (Lax799700.Common.SatOcc.LitTrue μ (preP s c x) true ↔ preVal μ c x s) := fun c x s => ⟨Iff.rfl, Iff.rfl⟩
  have hg : ∀ i c x s, Lax799700.Common.SatOcc.LitTrue μ (gP i s c x) true ↔ gVal μ i c x s := fun _ _ _ _ => Iff.rfl
  have hvar : ∀ x s, Lax799700.Common.SatOcc.LitTrue μ (varP x) s ↔ Lax799700.Common.SatOcc.LitTrue (varVal μ) x s := fun _ _ => Iff.rfl
  have hvarn : ∀ x s, Lax799700.Common.SatOcc.LitTrue μ (varP x) (!s) ↔ ¬Lax799700.Common.SatOcc.LitTrue (varVal μ) x s := fun x s =>
    litTrue_not.trans (not_congr (hvar x s))
  -- the content of each clause, propositionally
  have hkd : ∀ {c x s}, MinOcc c x s →
      (OneInAt μ (OTag.kd s, ![c, x]) ↔ (preVal μ c x s ↔ Lax799700.Common.SatOcc.LitTrue (varVal μ) x s)) := by
    intro c x s hmin
    rw [oneInAt_two (occIn_kd hmin) (ne_of_tag (by intro h; cases h)),
      (hpre c x s).1, hvar x s]
    by_cases hz : preVal μ c x s <;> by_cases hl : Lax799700.Common.SatOcc.LitTrue (varVal μ) x s <;> simp [hz, hl]
  have htop : ∀ {c x s}, MaxOcc c x s →
      (OneInAt μ (OTag.top s, ![c, x]) ↔ preVal μ c x s) := by
    intro c x s hmax
    rw [oneInAt_one (occIn_top hmax)]
    exact (hpre c x s).2
  have hgate : ∀ {c y t x s}, SuccOcc c y t x s →
      ((OneInAt μ (OTag.gk .a s, ![c, x]) ∧ OneInAt μ (OTag.gk .b s, ![c, x]) ∧
          OneInAt μ (OTag.gk .c s, ![c, x])) ↔
        (gVal μ .tt c x s ↔ preVal μ c y t ∧ Lax799700.Common.SatOcc.LitTrue (varVal μ) x s) ∧
          (gVal μ .tf c x s ↔ preVal μ c y t ∧ ¬Lax799700.Common.SatOcc.LitTrue (varVal μ) x s) ∧
          (gVal μ .ft c x s ↔ ¬preVal μ c y t ∧ Lax799700.Common.SatOcc.LitTrue (varVal μ) x s) ∧
          (preVal μ c x s ↔ preVal μ c y t ∨ Lax799700.Common.SatOcc.LitTrue (varVal μ) x s)) := by
    intro c y t x s hsucc
    have hch := chained_of_succOcc hsucc
    have hA := oneInAt_three (μ := μ) (occIn_ka hsucc) (ne_of_tag (by intro h; cases h))
      (ne_of_tag (by intro h; cases h)) (ne_of_tag (by intro h; cases h))
    have hB := oneInAt_three (μ := μ) (occIn_kb hch) (ne_of_tag (by intro h; cases h))
      (ne_of_tag (by intro h; cases h)) (ne_of_tag (by intro h; cases h))
    have hC := oneInAt_four (μ := μ) (occIn_kc hch) (ne_of_tag (by intro h; cases h))
      (ne_of_tag (by intro h; cases h)) (ne_of_tag (by intro h; cases h))
      (ne_of_tag (by intro h; cases h)) (ne_of_tag (by intro h; cases h))
      (ne_of_tag (by intro h; cases h))
    rw [(hpre c y t).1, hg, hg] at hA
    rw [hvarn x s, hg, hg] at hB
    rw [(hpre c x s).1, hg, hg, hg] at hC
    rw [hA, hB, hC]
    exact gate_prop _ _ _ _ _ _
  rw [oneInProper_iff]
  constructor
  · intro h
    have hK : ∀ (t : OTag) (c x : A), ClauseSem t ![c, x] → OneInAt μ (t, ![c, x]) :=
      fun t c x hcl => h _ ((isClause_iff _ _).mpr hcl)
    refine ⟨fun c x s hmin => (hkd hmin).mp (hK _ c x hmin), fun c y t x s hsucc => ?_,
      fun c x s hmax => (htop hmax).mp (hK _ c x hmax), fun c hemp => ?_⟩
    · have hch := chained_of_succOcc hsucc
      exact (hgate hsucc).mp ⟨hK (.gk .a s) c x hch, hK (.gk .b s) c x hch,
        hK (.gk .c s) c x hch⟩
    · exact not_oneInAt_of_empty (not_occIn_empty (w := fun _ => c))
        (h (OTag.empty, fun _ => c) ((isClause_iff _ _).mpr ⟨rfl, hemp⟩))
  · rintro h ⟨t, w⟩ hcl
    have hcl' : ClauseSem t w := (isClause_iff t w).mp hcl
    rw [← eta2 w]
    cases t
    case gk k s =>
      obtain ⟨y, t, hsucc⟩ := exists_succOcc hcl'
      have hall := (hgate hsucc).mpr (h.gate _ _ _ _ _ hsucc)
      cases k
      exacts [hall.1, hall.2.1, hall.2.2]
    case kd s => exact (hkd hcl').mpr (h.first _ _ _ hcl')
    case top s => exact (htop hcl').mpr (h.last _ _ _ hcl')
    case empty => exact absurd hcl'.2 (h.nonempty _)
    all_goals exact hcl'.elim

end Assignments

/-! ### The variables of the interpreted instance -/

section Occurring

variable {A : Type} [instS : Lax904597.Sat.sat.Structure A] [instO : LinearOrder A]

/-- The elements of the interpreted instance that are variables of it: the
copies of the variables of the input, the prefix variables of its occurrences,
and the case variables of its occurrences that have a predecessor. -/
def OccElem : OTag → (Fin 2 → A) → Prop
  | .var, w => w 0 = w 1 ∧ ∃ c s, Lax799700.Common.SatOcc.OccIn c (w 0) s
  | .pre t, w => Lax799700.Common.SatOcc.OccIn (w 0) (w 1) t
  | .g _ t, w => Chained (w 0) (w 1) t
  | _, _ => False

theorem posSem_occElem {t te : OTag} {w we : Fin 2 → A} (h : PosSem t te w we) :
    OccElem te we := by
  cases t <;> cases te <;> try exact h.elim
  case gk.var k s =>
    obtain ⟨-, hown, hch⟩ := h
    exact ⟨hown.1, w 0, s, by rw [hown.2]; exact hch.occIn⟩
  case gk.g k s i t =>
    obtain ⟨⟨-, rfl⟩, hsame, hch⟩ := h
    change Chained (we 0) (we 1) t
    rw [← hsame.1, ← hsame.2]
    exact hch
  case kd.var s =>
    obtain ⟨-, hown, hmin⟩ := h
    exact ⟨hown.1, w 0, s, by rw [hown.2]; exact hmin.occIn⟩
  case top.pre s t =>
    obtain ⟨rfl, hsame, hmax⟩ := h
    change Lax799700.Common.SatOcc.OccIn (we 0) (we 1) t
    rw [← hsame.1, ← hsame.2]
    exact hmax.occIn

theorem negSem_occElem {t te : OTag} {w we : Fin 2 → A} (h : NegSem t te w we) :
    OccElem te we := by
  cases t <;> cases te <;> try exact h.elim
  case gk.var k s =>
    obtain ⟨-, hown, hch⟩ := h
    exact ⟨hown.1, w 0, s, by rw [hown.2]; exact hch.occIn⟩
  case gk.pre k s t =>
    change Lax799700.Common.SatOcc.OccIn (we 0) (we 1) t
    rcases h with ⟨-, hpred⟩ | ⟨⟨-, rfl⟩, hsame, hch⟩
    · rw [← hpred.1]
      exact hpred.2.1
    · rw [← hsame.1, ← hsame.2]
      exact hch.occIn
  case kd.var s =>
    obtain ⟨-, hown, hmin⟩ := h
    exact ⟨hown.1, w 0, s, by rw [hown.2]; exact hmin.occIn⟩
  case kd.pre s t =>
    obtain ⟨rfl, hsame, hmin⟩ := h
    change Lax799700.Common.SatOcc.OccIn (we 0) (we 1) t
    rw [← hsame.1, ← hsame.2]
    exact hmin.occIn

/-- **The variables of the interpreted instance**, characterized. -/
theorem satOccurs_iff (te : OTag) (we : Fin 2 → A) :
    Lax366625.CountingSat.SatOccurs (interp.Map A) (te, we) ↔ OccElem te we := by
  constructor
  · rintro ⟨⟨t, w⟩, -, hp | hn⟩
    · exact posSem_occElem ((posIn_iff _ _ _ _).mp hp)
    · exact negSem_occElem ((negIn_iff _ _ _ _).mp hn)
  · intro h
    cases te
    case var =>
      obtain ⟨hd, c, s, hocc⟩ := h
      by_cases hmin : MinOcc c (we 0) s
      · refine ⟨(OTag.kd s, ![c, we 0]), (isClause_iff _ _).mpr hmin, ?_⟩
        cases s
        · exact Or.inr ((negIn_iff _ _ _ _).mpr ⟨rfl, ⟨hd, rfl⟩, hmin⟩)
        · exact Or.inl ((posIn_iff _ _ _ _).mpr ⟨rfl, ⟨hd, rfl⟩, hmin⟩)
      · have hch : Chained c (we 0) s := ⟨hocc, hmin⟩
        refine ⟨(OTag.gk .b s, ![c, we 0]), (isClause_iff _ _).mpr hch, ?_⟩
        cases s
        · exact Or.inl ((posIn_iff _ _ _ _).mpr ⟨⟨rfl, rfl⟩, ⟨hd, rfl⟩, hch⟩)
        · exact Or.inr ((negIn_iff _ _ _ _).mpr ⟨⟨rfl, rfl⟩, ⟨hd, rfl⟩, hch⟩)
    case pre t =>
      by_cases hmin : MinOcc (we 0) (we 1) t
      · exact ⟨(OTag.kd t, we), (isClause_iff _ _).mpr hmin,
          Or.inr ((negIn_iff _ _ _ _).mpr ⟨rfl, ⟨rfl, rfl⟩, hmin⟩)⟩
      · have hch : Chained (we 0) (we 1) t := ⟨h, hmin⟩
        exact ⟨(OTag.gk .c t, we), (isClause_iff _ _).mpr hch,
          Or.inr ((negIn_iff _ _ _ _).mpr (Or.inr ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, hch⟩))⟩
    case g i t =>
      exact ⟨(OTag.gk .c t, we), (isClause_iff _ _).mpr h,
        Or.inl ((posIn_iff _ _ _ _).mpr ⟨⟨by cases i <;> rfl, rfl⟩, ⟨rfl, rfl⟩, h⟩)⟩
    all_goals exact h.elim

end Occurring

/-! ### Exactly-one models of the interpreted instance are models of the input -/

section Models

variable {A : Type} [instS : Lax904597.Sat.sat.Structure A] [instO : LinearOrder A] [Finite A]

/-- The assignment of the interpreted instance determined by an assignment of
the input, before its restriction to the variables of the instance. -/
def canon (ν : A → Prop) : OTag × (Fin 2 → A) → Prop
  | (.var, w) => ν (w 0)
  | (.pre s, w) => PrefixOr ν (w 0) (w 1) s
  | (.g .tt s, w) => PrefixOrStrict ν (w 0) (w 1) s ∧ Lax799700.Common.SatOcc.LitTrue ν (w 1) s
  | (.g .tf s, w) => PrefixOrStrict ν (w 0) (w 1) s ∧ ¬Lax799700.Common.SatOcc.LitTrue ν (w 1) s
  | (.g .ft s, w) => ¬PrefixOrStrict ν (w 0) (w 1) s ∧ Lax799700.Common.SatOcc.LitTrue ν (w 1) s
  | _ => False

omit instS instO [Finite A] in
theorem val_congr {μ : interp.Map A → Prop} (t : OTag) {u u' : Fin 2 → A} (h : u = u') :
    μ (t, u) ↔ μ (t, u') := by
  subst h
  rfl

/-- **A satisfying assignment has a gate valuation.** -/
theorem gateVal_canon {ν : A → Prop}
    (hν : ∀ c, Lax799700.Common.SatOcc.IsCl c → ∃ x s, Lax799700.Common.SatOcc.OccIn c x s ∧ Lax799700.Common.SatOcc.LitTrue ν x s) :
    GateVal (varVal (canon ν)) (preVal (canon ν)) (gVal (canon ν)) := by
  have hpv := prefixVal_prefixOr hν
  refine ⟨fun c x s hmin => ?_, fun c y t x s hsucc => ?_, hpv.last, hpv.nonempty⟩
  · change PrefixOr ν c x s ↔ Lax799700.Common.SatOcc.LitTrue ν x s
    rw [prefixOr_iff hmin.occIn]
    exact ⟨fun h => h.resolve_left (not_prefixOrStrict_min hmin), Or.inr⟩
  · have hps : PrefixOrStrict ν c x s ↔ PrefixOr ν c y t := prefixOrStrict_succ hsucc
    refine ⟨and_congr hps Iff.rfl, and_congr hps Iff.rfl, and_congr (not_congr hps) Iff.rfl, ?_⟩
    change PrefixOr ν c x s ↔ PrefixOr ν c y t ∨ Lax799700.Common.SatOcc.LitTrue ν x s
    rw [prefixOr_iff hsucc.2.1, hps]

variable (A) in
/-- **The exactly-one models of the interpreted instance are the models of the
input**, bijectively. -/
noncomputable def modelEquiv :
    {ν : A → Prop // Lax366625.CountingSat.SatModel A ν} ≃
      {μ : interp.Map A → Prop // Lax280166.CountingSatVariants.OneInModel (interp.Map A) μ} where
  toFun ν := ⟨fun e => canon ν.1 e ∧ Lax366625.CountingSat.SatOccurs (interp.Map A) e,
    oneInModel_restrict (oneInProper_iff_gateVal.mpr
      (gateVal_canon (SharpSatToThreeSat.satModel_occ ν.2)))⟩
  invFun μ := ⟨varVal μ.1, by
    have hpv := (oneInProper_iff_gateVal.mp μ.2.1).prefixVal
    refine ⟨fun c hc => ?_, fun x hx => ?_⟩
    · obtain ⟨x, s, hocc, hT⟩ := hpv.exists_litTrue hc
      cases s
      · exact ⟨x, Or.inr ⟨hocc.2, hT⟩⟩
      · exact ⟨x, Or.inl ⟨hocc.2, hT⟩⟩
    · exact (SharpSatToThreeSat.satOccurs_iff_occIn x).mpr
        ((satOccurs_iff _ _).mp (μ.2.2 _ hx)).2⟩
  left_inv := by
    rintro ⟨ν, hν⟩
    refine Subtype.ext (funext fun x => propext ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩)
    exact (satOccurs_iff _ _).mpr
      ⟨rfl, (SharpSatToThreeSat.satOccurs_iff_occIn x).mp (hν.2 x h)⟩
  right_inv := by
    rintro ⟨μ, hμ⟩
    have hgv := oneInProper_iff_gateVal.mp hμ.1
    have hpv := hgv.prefixVal
    refine Subtype.ext (funext fun e => propext ?_)
    obtain ⟨te, we⟩ := e
    suffices h : OccElem te we → (canon (varVal μ) (te, we) ↔ μ (te, we)) from
      ⟨fun ⟨hc, ho⟩ => (h ((satOccurs_iff _ _).mp ho)).mp hc,
        fun hv => ⟨(h ((satOccurs_iff _ _).mp (hμ.2 _ hv))).mpr hv, hμ.2 _ hv⟩⟩
    intro ho
    cases te
    case var =>
      have hwe : (fun _ => we 0 : Fin 2 → A) = we := by
        funext k
        fin_cases k
        · rfl
        · exact ho.1
      exact val_congr OTag.var hwe
    case pre t =>
      exact ((hpv.iff_prefixOr (we 0) (we 1) t ho).symm).trans
        (val_congr (OTag.pre t) (eta2 we))
    case g i t =>
      obtain ⟨y, t', hsucc⟩ := exists_succOcc ho
      have hz : preVal μ (we 0) y t' ↔ PrefixOrStrict (varVal μ) (we 0) (we 1) t :=
        (hpv.iff_prefixOr _ _ _ hsucc.1).trans (prefixOrStrict_succ hsucc).symm
      obtain ⟨h₁, h₂, h₃, -⟩ := hgv.gate _ _ _ _ _ hsucc
      cases i
      · exact ((h₁.trans (and_congr hz Iff.rfl)).symm).trans (val_congr _ (eta2 we))
      · exact ((h₂.trans (and_congr hz Iff.rfl)).symm).trans (val_congr _ (eta2 we))
      · exact ((h₃.trans (and_congr (not_congr hz) Iff.rfl)).symm).trans
          (val_congr _ (eta2 we))
    all_goals exact ho.elim

end Models

/-- **Correctness of the interpretation, for counting**: the interpreted
instance has as many exactly-one models as the input has models. -/
theorem sharpOneInSat_map (A : Type) [Lax904597.Sat.sat.Structure A] [LinearOrder A] [Finite A] :
    SharpOneInSAT (interp.Map A) = SharpSAT A := by
  rw [sharpOneInSat_apply, sharpSat_apply]
  exact (Nat.card_congr (modelEquiv A)).symm

end SharpSatToOneIn

open SharpSatToOneIn in
/-- **#SAT reduces parsimoniously to #1-in-SAT.** -/
noncomputable def sharpSat_ordered_parsimonious_sharpOneInSat :
    SharpSAT ≤ᵖ[≤] SharpOneInSAT where
  Tag := OTag
  dim := 2
  toInterpretation := interp
  correct A _ _ _ _ := (sharpOneInSat_map A).symm

/-- #1-in-SAT is parsimoniously `#P`-hard. -/
theorem sharpOneInSat_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpOneInSAT :=
  SharpP.parsimoniousHard_of_orderedParsimonious sharpSat_ordered_parsimonious_sharpOneInSat
    sharpSat_sharpP_parsimoniousHard

/-- **#1-in-SAT is parsimoniously `#P`-complete.** -/
theorem sharpOneInSat_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpOneInSAT :=
  ⟨sharpOneInSat_mem_sharpP, sharpOneInSat_sharpP_parsimoniousHard⟩

end Lax280166Proofs.DescriptiveComplexity


