/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.OccurrenceFormulas
import Lax859101Proofs.DescriptiveComplexity.OccurrencePrefix
import Lax859101Proofs.DescriptiveComplexity.Problems.ThreeSat.Counting
import Lax859101Proofs.DescriptiveComplexity.Problems.Sat.CountingHardness
import Mathlib.Data.Fintype.Pigeonhole
import Lax859101Proofs.DescriptiveComplexity.Counting.Subtractive
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

namespace Lax366625.CountingSat
end Lax366625.CountingSat

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc

namespace Lax799700.ThreeSat
end Lax799700.ThreeSat

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax859101Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax799700.ThreeSat (WidthAtMostThree)
end Lax859101Proofs.DescriptiveComplexity

namespace Lax859101Proofs.DescriptiveComplexity
export Lax366625.CountingSat (SatModel SatOccurs)
end Lax859101Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

namespace Lax859101Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (IsCl LitTrue OccIn)
end Lax859101Proofs.DescriptiveComplexity.SatOcc

/-!
# #SAT reduces parsimoniously to #3SAT

The clause-splitting reduction of
`DescriptiveComplexity.Problems.ThreeSat.FromSat` threads fresh variables along the
occurrences of a clause, and leaves them free once the clause is satisfied; it
preserves satisfiability, not the number of models. This file is the variant
that preserves it, `DescriptiveComplexity.sharpSat_ordered_parsimonious_sharpThreeSat`,
which makes #3SAT parsimoniously `#P`-complete
(`DescriptiveComplexity.sharpThreeSat_sharpP_parsimoniousComplete`).

For each occurrence `(x, s)` of a clause `c`, the interpretation
(`DescriptiveComplexity.SharpSatToThreeSat.interp`, dimension 2) has a variable
`z = (.pre s, (c, x))`, forced to be the truth of the disjunction of the
occurrences of `c` up to `(x, s)` by three clauses, with `z'` the variable of
the preceding occurrence when there is one:

* `(.k0 s, (c, x))`: `¬z ∨ ℓ ∨ z'`;
* `(.k1 s, (c, x))`: `z ∨ ¬ℓ`;
* `(.k2 s, (c, x))`: `z ∨ ¬z'`;

and the last occurrence of `c` carries the unit clause `(.top s, (c, x))`: `z`.
Empty clauses are copied as empty clauses. That such `z` are determined by the
assignment, and exist exactly when it satisfies every clause, is the
interpretation-free content of `DescriptiveComplexity.OccurrencePrefix`.
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

namespace SharpSatToThreeSat

open Language Structure SatOcc

/-- Tags of the parsimonious clause-splitting interpretation. -/
inductive PTag : Type
  /-- `(.var, (x, x))` is the copy of the propositional variable `x`. -/
  | var
  /-- `(.pre s, (c, x))` is the prefix variable of the occurrence `(x, s)` of
  the clause `c`. -/
  | pre (s : Bool)
  /-- The clause `¬z ∨ ℓ ∨ z'` of an occurrence. -/
  | k0 (s : Bool)
  /-- The clause `z ∨ ¬ℓ` of an occurrence. -/
  | k1 (s : Bool)
  /-- The clause `z ∨ ¬z'` of an occurrence that has a predecessor. -/
  | k2 (s : Bool)
  /-- The unit clause `z` of the last occurrence of a clause. -/
  | top (s : Bool)
  /-- `(.empty, (c, c))` is the copy of the empty clause `c`. -/
  | empty
  deriving DecidableEq, Fintype, Nonempty

/-- The second argument is the variable copy of the variable of the first. -/
def ownVarF : satOrd.Formula (Fin 2 × Fin 2) := eqF (1, 0) (1, 1) ⊓ eqF (1, 0) (0, 1)

/-- The two arguments sit on the same pair. -/
def sameF : satOrd.Formula (Fin 2 × Fin 2) := eqF (0, 0) (1, 0) ⊓ eqF (0, 1) (1, 1)

/-- The second argument sits on the occurrence `(y, t)` of the same clause
immediately preceding the occurrence `(x, s)` of the first. -/
noncomputable def predF (t s : Bool) : satOrd.Formula (Fin 2 × Fin 2) :=
  eqF (0, 0) (1, 0) ⊓ succOccF t s (0, 0) (1, 1) (0, 1)

/-- Defining formula for `satIsClause`. -/
noncomputable def isClauseF : PTag → satOrd.Formula (Fin 1 × Fin 2)
  | .k0 s => occF s (0, 0) (0, 1)
  | .k1 s => occF s (0, 0) (0, 1)
  | .k2 s => chainedF s (0, 0) (0, 1)
  | .top s => maxOccF s (0, 0) (0, 1)
  | .empty => eqF (0, 0) (0, 1) ⊓ emptyClF (0, 0)
  | _ => ⊥

/-- Defining formula for `satPosIn`. -/
noncomputable def posInF : PTag → PTag → satOrd.Formula (Fin 2 × Fin 2)
  | .k0 s, .var => if s then ownVarF ⊓ occF true (0, 0) (0, 1) else ⊥
  | .k0 s, .pre t => predF t s
  | .k1 s, .var => if s then ⊥ else ownVarF ⊓ occF false (0, 0) (0, 1)
  | .k1 s, .pre t => if t = s then sameF ⊓ occF s (0, 0) (0, 1) else ⊥
  | .k2 s, .pre t => if t = s then sameF ⊓ chainedF s (0, 0) (0, 1) else ⊥
  | .top s, .pre t => if t = s then sameF ⊓ maxOccF s (0, 0) (0, 1) else ⊥
  | _, _ => ⊥

/-- Defining formula for `satNegIn`. -/
noncomputable def negInF : PTag → PTag → satOrd.Formula (Fin 2 × Fin 2)
  | .k0 s, .var => if s then ⊥ else ownVarF ⊓ occF false (0, 0) (0, 1)
  | .k0 s, .pre t => if t = s then sameF ⊓ occF s (0, 0) (0, 1) else ⊥
  | .k1 s, .var => if s then ownVarF ⊓ occF true (0, 0) (0, 1) else ⊥
  | .k2 s, .pre t => predF t s
  | _, _ => ⊥

/-- The parsimonious clause-splitting interpretation. -/
noncomputable def interp : Lax904597.Interpretations.FOInterpretation satOrd Lax904597.Sat.sat PTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun t => isClauseF (t 0)
    | _, .posIn => fun t => posInF (t 0) (t 1)
    | _, .negIn => fun t => negInF (t 0) (t 1)

/-! ### Characterization of the interpreted relations -/

section Characterizations

variable {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A]

/-- The semantic content of `isClauseF`. -/
def ClauseSem : PTag → (Fin 2 → A) → Prop
  | .k0 s, w => Lax799700.Common.SatOcc.OccIn (w 0) (w 1) s
  | .k1 s, w => Lax799700.Common.SatOcc.OccIn (w 0) (w 1) s
  | .k2 s, w => Chained (w 0) (w 1) s
  | .top s, w => MaxOcc (w 0) (w 1) s
  | .empty, w => w 0 = w 1 ∧ EmptyCl (w 0)
  | _, _ => False

/-- The second pair is the diagonal on the variable of the first. -/
def OwnVar (w₁ w₂ : Fin 2 → A) : Prop := w₂ 0 = w₂ 1 ∧ w₂ 0 = w₁ 1

/-- The two pairs are the same. -/
def Same (w₁ w₂ : Fin 2 → A) : Prop := w₁ 0 = w₂ 0 ∧ w₁ 1 = w₂ 1

/-- The second pair is the predecessor occurrence of the first. -/
def Pred (t s : Bool) (w₁ w₂ : Fin 2 → A) : Prop :=
  w₁ 0 = w₂ 0 ∧ SuccOcc (w₁ 0) (w₂ 1) t (w₁ 1) s

/-- The semantic content of `posInF`. -/
def PosSem : PTag → PTag → (Fin 2 → A) → (Fin 2 → A) → Prop
  | .k0 s, .var, w₁, w₂ => s = true ∧ OwnVar w₁ w₂ ∧ Lax799700.Common.SatOcc.OccIn (w₁ 0) (w₁ 1) true
  | .k0 s, .pre t, w₁, w₂ => Pred t s w₁ w₂
  | .k1 s, .var, w₁, w₂ => s = false ∧ OwnVar w₁ w₂ ∧ Lax799700.Common.SatOcc.OccIn (w₁ 0) (w₁ 1) false
  | .k1 s, .pre t, w₁, w₂ => t = s ∧ Same w₁ w₂ ∧ Lax799700.Common.SatOcc.OccIn (w₁ 0) (w₁ 1) s
  | .k2 s, .pre t, w₁, w₂ => t = s ∧ Same w₁ w₂ ∧ Chained (w₁ 0) (w₁ 1) s
  | .top s, .pre t, w₁, w₂ => t = s ∧ Same w₁ w₂ ∧ MaxOcc (w₁ 0) (w₁ 1) s
  | _, _, _, _ => False

/-- The semantic content of `negInF`. -/
def NegSem : PTag → PTag → (Fin 2 → A) → (Fin 2 → A) → Prop
  | .k0 s, .var, w₁, w₂ => s = false ∧ OwnVar w₁ w₂ ∧ Lax799700.Common.SatOcc.OccIn (w₁ 0) (w₁ 1) false
  | .k0 s, .pre t, w₁, w₂ => t = s ∧ Same w₁ w₂ ∧ Lax799700.Common.SatOcc.OccIn (w₁ 0) (w₁ 1) s
  | .k1 s, .var, w₁, w₂ => s = true ∧ OwnVar w₁ w₂ ∧ Lax799700.Common.SatOcc.OccIn (w₁ 0) (w₁ 1) true
  | .k2 s, .pre t, w₁, w₂ => Pred t s w₁ w₂
  | _, _, _, _ => False

theorem isClause_iff (t : PTag) (w : Fin 2 → A) :
    RelMap (M := interp.Map A) Lax904597.Sat.satIsClause ![(t, w)] ↔ ClauseSem t w := by
  rw [FOInterpretation.relMap_map]
  cases t <;> simp [interp, isClauseF, ClauseSem]

theorem posIn_iff (t₁ t₂ : PTag) (w₁ w₂ : Fin 2 → A) :
    RelMap (M := interp.Map A) Lax904597.Sat.satPosIn ![(t₁, w₁), (t₂, w₂)] ↔ PosSem t₁ t₂ w₁ w₂ := by
  rw [FOInterpretation.relMap_map]
  cases t₁ <;> cases t₂ <;>
    first
      | exact Iff.rfl
      | (rename_i s t
         cases s <;> cases t <;>
           simp [interp, posInF, PosSem, ownVarF, OwnVar, predF, Pred, sameF, Same, and_assoc])

theorem negIn_iff (t₁ t₂ : PTag) (w₁ w₂ : Fin 2 → A) :
    RelMap (M := interp.Map A) Lax904597.Sat.satNegIn ![(t₁, w₁), (t₂, w₂)] ↔ NegSem t₁ t₂ w₁ w₂ := by
  rw [FOInterpretation.relMap_map]
  cases t₁ <;> cases t₂ <;>
    first
      | exact Iff.rfl
      | (rename_i s t
         cases s <;> cases t <;>
           simp [interp, negInF, NegSem, ownVarF, OwnVar, predF, Pred, sameF, Same, and_assoc])

end Characterizations

/-! ### Assignments of the split, read as prefix valuations -/

section Assignments

variable {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A]

omit [Lax904597.Sat.sat.Structure A] [LinearOrder A] in
theorem eta2 (w : Fin 2 → A) : (![w 0, w 1] : Fin 2 → A) = w := by
  funext k
  fin_cases k <;> rfl

omit [Lax904597.Sat.sat.Structure A] [LinearOrder A] in
theorem ownVar_eq {w₁ w₂ : Fin 2 → A} (h : OwnVar w₁ w₂) : w₂ = fun _ => w₁ 1 := by
  funext k
  fin_cases k
  · exact h.2
  · exact h.1.symm.trans h.2

omit [Lax904597.Sat.sat.Structure A] [LinearOrder A] in
theorem same_eq {w₁ w₂ : Fin 2 → A} (h : Same w₁ w₂) : w₂ = w₁ := by
  funext k
  fin_cases k
  · exact h.1.symm
  · exact h.2.symm

theorem pred_eq {t s : Bool} {w₁ w₂ : Fin 2 → A} (h : Pred t s w₁ w₂) :
    w₂ = ![w₁ 0, w₂ 1] := by
  funext k
  fin_cases k
  · exact h.1.symm
  · rfl

variable (ν' : interp.Map A → Prop)

/-- The assignment read on the variable copies. -/
def varVal (x : A) : Prop := ν' (PTag.var, fun _ => x)

/-- The assignment read on the prefix variables. -/
def preVal (c x : A) (s : Bool) : Prop := ν' (PTag.pre s, ![c, x])

/-- The clause `K` contains a literal made true by `ν'`. -/
def HasTrue (K : interp.Map A) : Prop :=
  ∃ e : interp.Map A, (RelMap Lax904597.Sat.satPosIn ![K, e] ∧ ν' e) ∨ (RelMap Lax904597.Sat.satNegIn ![K, e] ∧ ¬ν' e)

variable {ν'}

omit [Lax904597.Sat.sat.Structure A] [LinearOrder A] in
theorem val_congr (t : PTag) {u u' : Fin 2 → A} (h : u = u') : ν' (t, u) ↔ ν' (t, u') := by
  subst h
  rfl

theorem hasTrue_k0 {c x : A} {s : Bool} :
    HasTrue ν' (PTag.k0 s, ![c, x]) ↔
      Lax799700.Common.SatOcc.OccIn c x s ∧ (¬preVal ν' c x s ∨ Lax799700.Common.SatOcc.LitTrue (varVal ν') x s) ∨
        ∃ y t, SuccOcc c y t x s ∧ preVal ν' c y t := by
  constructor
  · rintro ⟨⟨te, we⟩, ⟨hp, hv⟩ | ⟨hn, hv⟩⟩
    · rw [posIn_iff] at hp
      cases te
      case var =>
        obtain ⟨rfl, hown, hocc⟩ := hp
        obtain rfl := ownVar_eq hown
        exact Or.inl ⟨hocc, Or.inr hv⟩
      case pre t =>
        exact Or.inr ⟨we 1, t, hp.2, (val_congr (PTag.pre t) (pred_eq hp)).mp hv⟩
      all_goals exact hp.elim
    · rw [negIn_iff] at hn
      cases te
      case var =>
        obtain ⟨rfl, hown, hocc⟩ := hn
        obtain rfl := ownVar_eq hown
        exact Or.inl ⟨hocc, Or.inr hv⟩
      case pre t =>
        obtain ⟨rfl, hsame, hocc⟩ := hn
        obtain rfl := same_eq hsame
        exact Or.inl ⟨hocc, Or.inl hv⟩
      all_goals exact hn.elim
  · rintro (⟨hocc, hz | hl⟩ | ⟨y, t, hsucc, hz⟩)
    · exact ⟨(PTag.pre s, ![c, x]), Or.inr ⟨(negIn_iff _ _ _ _).mpr ⟨rfl, ⟨rfl, rfl⟩, hocc⟩, hz⟩⟩
    · cases s
      · exact ⟨(PTag.var, fun _ => x),
          Or.inr ⟨(negIn_iff _ _ _ _).mpr ⟨rfl, ⟨rfl, rfl⟩, hocc⟩, hl⟩⟩
      · exact ⟨(PTag.var, fun _ => x),
          Or.inl ⟨(posIn_iff _ _ _ _).mpr ⟨rfl, ⟨rfl, rfl⟩, hocc⟩, hl⟩⟩
    · exact ⟨(PTag.pre t, ![c, y]), Or.inl ⟨(posIn_iff _ _ _ _).mpr ⟨rfl, hsucc⟩, hz⟩⟩

theorem hasTrue_k1 {c x : A} {s : Bool} :
    HasTrue ν' (PTag.k1 s, ![c, x]) ↔
      Lax799700.Common.SatOcc.OccIn c x s ∧ (preVal ν' c x s ∨ ¬Lax799700.Common.SatOcc.LitTrue (varVal ν') x s) := by
  constructor
  · rintro ⟨⟨te, we⟩, ⟨hp, hv⟩ | ⟨hn, hv⟩⟩
    · rw [posIn_iff] at hp
      cases te
      case var =>
        obtain ⟨rfl, hown, hocc⟩ := hp
        obtain rfl := ownVar_eq hown
        exact ⟨hocc, Or.inr (not_not_intro hv)⟩
      case pre t =>
        obtain ⟨rfl, hsame, hocc⟩ := hp
        obtain rfl := same_eq hsame
        exact ⟨hocc, Or.inl hv⟩
      all_goals exact hp.elim
    · rw [negIn_iff] at hn
      cases te
      case var =>
        obtain ⟨rfl, hown, hocc⟩ := hn
        obtain rfl := ownVar_eq hown
        exact ⟨hocc, Or.inr hv⟩
      all_goals exact hn.elim
  · rintro ⟨hocc, hz | hl⟩
    · exact ⟨(PTag.pre s, ![c, x]), Or.inl ⟨(posIn_iff _ _ _ _).mpr ⟨rfl, ⟨rfl, rfl⟩, hocc⟩, hz⟩⟩
    · cases s
      · exact ⟨(PTag.var, fun _ => x),
          Or.inl ⟨(posIn_iff _ _ _ _).mpr ⟨rfl, ⟨rfl, rfl⟩, hocc⟩, not_not.mp hl⟩⟩
      · exact ⟨(PTag.var, fun _ => x),
          Or.inr ⟨(negIn_iff _ _ _ _).mpr ⟨rfl, ⟨rfl, rfl⟩, hocc⟩, hl⟩⟩

theorem hasTrue_k2 {c x : A} {s : Bool} :
    HasTrue ν' (PTag.k2 s, ![c, x]) ↔
      (Chained c x s ∧ preVal ν' c x s) ∨ ∃ y t, SuccOcc c y t x s ∧ ¬preVal ν' c y t := by
  constructor
  · rintro ⟨⟨te, we⟩, ⟨hp, hv⟩ | ⟨hn, hv⟩⟩
    · rw [posIn_iff] at hp
      cases te
      case pre t =>
        obtain ⟨rfl, hsame, hch⟩ := hp
        obtain rfl := same_eq hsame
        exact Or.inl ⟨hch, hv⟩
      all_goals exact hp.elim
    · rw [negIn_iff] at hn
      cases te
      case pre t =>
        exact Or.inr ⟨we 1, t, hn.2,
          fun hz => hv ((val_congr (PTag.pre t) (pred_eq hn)).mpr hz)⟩
      all_goals exact hn.elim
  · rintro (⟨hch, hz⟩ | ⟨y, t, hsucc, hz⟩)
    · exact ⟨(PTag.pre s, ![c, x]), Or.inl ⟨(posIn_iff _ _ _ _).mpr ⟨rfl, ⟨rfl, rfl⟩, hch⟩, hz⟩⟩
    · exact ⟨(PTag.pre t, ![c, y]), Or.inr ⟨(negIn_iff _ _ _ _).mpr ⟨rfl, hsucc⟩, hz⟩⟩

theorem hasTrue_top {c x : A} {s : Bool} :
    HasTrue ν' (PTag.top s, ![c, x]) ↔ MaxOcc c x s ∧ preVal ν' c x s := by
  constructor
  · rintro ⟨⟨te, we⟩, ⟨hp, hv⟩ | ⟨hn, hv⟩⟩
    · rw [posIn_iff] at hp
      cases te
      case pre t =>
        obtain ⟨rfl, hsame, hmax⟩ := hp
        obtain rfl := same_eq hsame
        exact ⟨hmax, hv⟩
      all_goals exact hp.elim
    · rw [negIn_iff] at hn
      cases te <;> exact hn.elim
  · rintro ⟨hmax, hz⟩
    exact ⟨(PTag.pre s, ![c, x]), Or.inl ⟨(posIn_iff _ _ _ _).mpr ⟨rfl, ⟨rfl, rfl⟩, hmax⟩, hz⟩⟩

theorem not_hasTrue_empty {w : Fin 2 → A} : ¬HasTrue ν' (PTag.empty, w) := by
  rintro ⟨⟨te, we⟩, ⟨hp, -⟩ | ⟨hn, -⟩⟩
  · rw [posIn_iff] at hp
    cases te <;> exact hp.elim
  · rw [negIn_iff] at hn
    cases te <;> exact hn.elim

variable [Finite A]

/-- **Every clause of the split has a true literal exactly when the assignment
is a prefix valuation**, read on the variable copies and the prefix
variables. -/
theorem allTrue_iff :
    (∀ K : interp.Map A, RelMap Lax904597.Sat.satIsClause ![K] → HasTrue ν' K) ↔
      PrefixVal (varVal ν') (preVal ν') := by
  constructor
  · intro h
    have hk0 : ∀ c x s, Lax799700.Common.SatOcc.OccIn c x s → HasTrue ν' (PTag.k0 s, ![c, x]) := fun c x s hocc =>
      h _ ((isClause_iff _ _).mpr hocc)
    have hk1 : ∀ c x s, Lax799700.Common.SatOcc.OccIn c x s → HasTrue ν' (PTag.k1 s, ![c, x]) := fun c x s hocc =>
      h _ ((isClause_iff _ _).mpr hocc)
    refine ⟨fun c x s hocc => ⟨fun hz => ?_, ?_⟩, fun c x s hmax => ?_, fun c hemp => ?_⟩
    · rcases hasTrue_k0.mp (hk0 c x s hocc) with ⟨-, hnz | hl⟩ | hpred
      · exact absurd hz hnz
      · exact Or.inl hl
      · exact Or.inr hpred
    · rintro (hl | ⟨y, t, hsucc, hzy⟩)
      · exact (hasTrue_k1.mp (hk1 c x s hocc)).2.resolve_right (not_not_intro hl)
      · have hch : Chained c x s := ⟨hocc, fun hmin => hmin.2 y t hsucc.1 hsucc.2.2.1⟩
        rcases hasTrue_k2.mp (h (PTag.k2 s, ![c, x]) ((isClause_iff _ _).mpr hch)) with
          ⟨-, hz⟩ | ⟨y', t', hsucc', hnz⟩
        · exact hz
        · obtain ⟨rfl, rfl⟩ := succOcc_left_unique hsucc hsucc'
          exact absurd hzy hnz
    · exact (hasTrue_top.mp (h (PTag.top s, ![c, x]) ((isClause_iff _ _).mpr hmax))).2
    · exact not_hasTrue_empty (h (PTag.empty, fun _ => c) ((isClause_iff _ _).mpr ⟨rfl, hemp⟩))
  · rintro h ⟨t, w⟩ hcl
    rw [isClause_iff] at hcl
    rw [← eta2 w]
    cases t
    case k0 s =>
      refine hasTrue_k0.mpr ?_
      by_cases hz : preVal ν' (w 0) (w 1) s
      · rcases (h.step _ _ _ hcl).mp hz with hl | hpred
        · exact Or.inl ⟨hcl, Or.inr hl⟩
        · exact Or.inr hpred
      · exact Or.inl ⟨hcl, Or.inl hz⟩
    case k1 s =>
      refine hasTrue_k1.mpr ⟨hcl, ?_⟩
      by_cases hl : Lax799700.Common.SatOcc.LitTrue (varVal ν') (w 1) s
      · exact Or.inl ((h.step _ _ _ hcl).mpr (Or.inl hl))
      · exact Or.inr hl
    case k2 s =>
      refine hasTrue_k2.mpr ?_
      obtain ⟨y, t, hsucc⟩ := exists_succOcc hcl
      by_cases hz : preVal ν' (w 0) y t
      · exact Or.inl ⟨hcl, (h.step _ _ _ hcl.occIn).mpr (Or.inr ⟨y, t, hsucc, hz⟩)⟩
      · exact Or.inr ⟨y, t, hsucc, hz⟩
    case top s => exact hasTrue_top.mpr ⟨hcl, h.last _ _ _ hcl⟩
    case empty => exact absurd hcl.2 (h.nonempty _)
    all_goals exact hcl.elim

end Assignments

/-! ### The variables of the split -/

section Occurring

variable {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A]

/-- The elements of the split that are variables of it: the copies of the
variables of the input, and the prefix variables of its occurrences. -/
def OccElem : PTag → (Fin 2 → A) → Prop
  | .var, w => w 0 = w 1 ∧ ∃ c s, Lax799700.Common.SatOcc.OccIn c (w 0) s
  | .pre t, w => Lax799700.Common.SatOcc.OccIn (w 0) (w 1) t
  | _, _ => False

theorem posSem_occElem {t te : PTag} {w we : Fin 2 → A} (h : PosSem t te w we) :
    OccElem te we := by
  cases t <;> cases te <;> try exact h.elim
  case k0.var s =>
    obtain ⟨-, hown, hocc⟩ := h
    exact ⟨hown.1, w 0, true, by rw [hown.2]; exact hocc⟩
  case k0.pre s t =>
    change Lax799700.Common.SatOcc.OccIn (we 0) (we 1) t
    rw [← h.1]
    exact h.2.1
  case k1.var s =>
    obtain ⟨-, hown, hocc⟩ := h
    exact ⟨hown.1, w 0, false, by rw [hown.2]; exact hocc⟩
  case k1.pre s t =>
    obtain ⟨rfl, hsame, hocc⟩ := h
    change Lax799700.Common.SatOcc.OccIn (we 0) (we 1) t
    rw [← hsame.1, ← hsame.2]
    exact hocc
  case k2.pre s t =>
    obtain ⟨rfl, hsame, hch⟩ := h
    change Lax799700.Common.SatOcc.OccIn (we 0) (we 1) t
    rw [← hsame.1, ← hsame.2]
    exact hch.occIn
  case top.pre s t =>
    obtain ⟨rfl, hsame, hmax⟩ := h
    change Lax799700.Common.SatOcc.OccIn (we 0) (we 1) t
    rw [← hsame.1, ← hsame.2]
    exact hmax.occIn

theorem negSem_occElem {t te : PTag} {w we : Fin 2 → A} (h : NegSem t te w we) :
    OccElem te we := by
  cases t <;> cases te <;> try exact h.elim
  case k0.var s =>
    obtain ⟨-, hown, hocc⟩ := h
    exact ⟨hown.1, w 0, false, by rw [hown.2]; exact hocc⟩
  case k0.pre s t =>
    obtain ⟨rfl, hsame, hocc⟩ := h
    change Lax799700.Common.SatOcc.OccIn (we 0) (we 1) t
    rw [← hsame.1, ← hsame.2]
    exact hocc
  case k1.var s =>
    obtain ⟨-, hown, hocc⟩ := h
    exact ⟨hown.1, w 0, true, by rw [hown.2]; exact hocc⟩
  case k2.pre s t =>
    change Lax799700.Common.SatOcc.OccIn (we 0) (we 1) t
    rw [← h.1]
    exact h.2.1

/-- **The variables of the split**, characterized. -/
theorem satOccurs_iff (te : PTag) (we : Fin 2 → A) :
    Lax366625.CountingSat.SatOccurs (interp.Map A) (te, we) ↔ OccElem te we := by
  constructor
  · rintro ⟨⟨t, w⟩, -, hp | hn⟩
    · exact posSem_occElem ((posIn_iff _ _ _ _).mp hp)
    · exact negSem_occElem ((negIn_iff _ _ _ _).mp hn)
  · intro h
    cases te
    case var =>
      obtain ⟨hd, c, s, hocc⟩ := h
      refine ⟨(PTag.k0 s, ![c, we 0]), (isClause_iff _ _).mpr hocc, ?_⟩
      cases s
      · exact Or.inr ((negIn_iff _ _ _ _).mpr ⟨rfl, ⟨hd, rfl⟩, hocc⟩)
      · exact Or.inl ((posIn_iff _ _ _ _).mpr ⟨rfl, ⟨hd, rfl⟩, hocc⟩)
    case pre t =>
      exact ⟨(PTag.k0 t, we), (isClause_iff _ _).mpr h,
        Or.inr ((negIn_iff _ _ _ _).mpr ⟨rfl, ⟨rfl, rfl⟩, h⟩)⟩
    all_goals exact h.elim

omit [LinearOrder A] in
theorem satOccurs_iff_occIn (x : A) : Lax366625.CountingSat.SatOccurs A x ↔ ∃ c s, Lax799700.Common.SatOcc.OccIn c x s := by
  constructor
  · rintro ⟨c, hc, hp | hn⟩
    · exact ⟨c, true, hc, hp⟩
    · exact ⟨c, false, hc, hn⟩
  · rintro ⟨c, s, hc, hs⟩
    cases s
    · exact ⟨c, hc, Or.inr hs⟩
    · exact ⟨c, hc, Or.inl hs⟩

end Occurring

/-! ### Models of the split are models of the input -/

section Models

variable {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A] [Finite A]

/-- The assignment of the split determined by an assignment of the input,
before its restriction to the variables of the split: variable copies follow
it, and a prefix variable is the truth of its prefix disjunction. -/
def canon (ν : A → Prop) : PTag × (Fin 2 → A) → Prop
  | (.var, w) => ν (w 0)
  | (.pre s, w) => PrefixOr ν (w 0) (w 1) s
  | _ => False

omit [LinearOrder A] [Finite A] in
theorem satModel_occ {ν : A → Prop} (h : Lax366625.CountingSat.SatModel A ν) :
    ∀ c : A, Lax799700.Common.SatOcc.IsCl c → ∃ x s, Lax799700.Common.SatOcc.OccIn c x s ∧ Lax799700.Common.SatOcc.LitTrue ν x s :=
  satClauses_occ h.1

variable (A) in
/-- **The models of the split are the models of the input**, bijectively: a
model of the input extends by the truth of its prefix disjunctions, and a
model of the split is recovered from its variable copies because the prefix
variables are determined. -/
noncomputable def modelEquiv :
    {ν : A → Prop // Lax366625.CountingSat.SatModel A ν} ≃
      {ν' : interp.Map A → Prop // Lax366625.CountingSat.SatModel (interp.Map A) ν'} where
  toFun ν := ⟨fun e => canon ν.1 e ∧ Lax366625.CountingSat.SatOccurs (interp.Map A) e,
    satModel_restrict ((allTrue_iff (ν' := canon ν.1)).mpr
      (prefixVal_prefixOr (satModel_occ ν.2)))⟩
  invFun ν' := ⟨varVal ν'.1, by
    have hpv := allTrue_iff.mp ν'.2.1
    refine ⟨fun c hc => ?_, fun x hx => ?_⟩
    · obtain ⟨x, s, hocc, hT⟩ := hpv.exists_litTrue hc
      cases s
      · exact ⟨x, Or.inr ⟨hocc.2, hT⟩⟩
      · exact ⟨x, Or.inl ⟨hocc.2, hT⟩⟩
    · exact (satOccurs_iff_occIn x).mpr ((satOccurs_iff _ _).mp (ν'.2.2 _ hx)).2⟩
  left_inv := by
    rintro ⟨ν, hν⟩
    refine Subtype.ext (funext fun x => propext ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩)
    exact (satOccurs_iff _ _).mpr ⟨rfl, (satOccurs_iff_occIn x).mp (hν.2 x h)⟩
  right_inv := by
    rintro ⟨ν', hν'⟩
    have hpv := allTrue_iff.mp hν'.1
    refine Subtype.ext (funext fun e => propext ?_)
    obtain ⟨te, we⟩ := e
    suffices h : OccElem te we → (canon (varVal ν') (te, we) ↔ ν' (te, we)) from
      ⟨fun ⟨hc, ho⟩ => (h ((satOccurs_iff _ _).mp ho)).mp hc,
        fun hv => ⟨(h ((satOccurs_iff _ _).mp (hν'.2 _ hv))).mpr hv, hν'.2 _ hv⟩⟩
    intro ho
    cases te
    case var =>
      have hwe : (fun _ => we 0 : Fin 2 → A) = we := by
        funext k
        fin_cases k
        · rfl
        · exact ho.1
      exact val_congr PTag.var hwe
    case pre t =>
      exact ((hpv.iff_prefixOr (we 0) (we 1) t ho).symm).trans
        (val_congr (PTag.pre t) (eta2 we))
    all_goals exact ho.elim

end Models

/-! ### The width bound -/

section Width

variable {A : Type} [Lax904597.Sat.sat.Structure A] [LinearOrder A]

/-- The literals of the split, with their sign. -/
def LitSem : Bool → PTag → PTag → (Fin 2 → A) → (Fin 2 → A) → Prop
  | true => PosSem
  | false => NegSem

theorem occIn_map_iff (t te : PTag) (w we : Fin 2 → A) (sg : Bool) :
    Lax799700.Common.SatOcc.OccIn (A := interp.Map A) (t, w) (te, we) sg ↔ ClauseSem t w ∧ LitSem sg t te w we := by
  cases sg
  · exact and_congr (isClause_iff t w) (negIn_iff t te w we)
  · exact and_congr (isClause_iff t w) (posIn_iff t te w we)

/-- A literal of the split is a variable copy or a prefix variable. -/
theorem litSem_tag {sg : Bool} {t te : PTag} {w we : Fin 2 → A} (h : LitSem sg t te w we) :
    te = .var ∨ ∃ a, te = .pre a := by
  cases t <;> cases sg <;> cases te <;>
    first
      | exact h.elim
      | exact Or.inl rfl
      | exact Or.inr ⟨_, rfl⟩

/-- A clause of the split has one variable copy among its literals, with one
sign. -/
theorem var_unique {sg sg' : Bool} {t : PTag} {w we we' : Fin 2 → A}
    (h : LitSem sg t .var w we) (h' : LitSem sg' t .var w we') : we = we' ∧ sg = sg' := by
  cases t <;> cases sg <;> cases sg' <;>
    first
      | exact h.elim
      | exact h'.elim
      | exact ⟨(ownVar_eq h.2.1).trans (ownVar_eq h'.2.1).symm, rfl⟩
      | exact absurd (h.1.symm.trans h'.1) (by decide)

theorem pred_unique {a a' s : Bool} {w we we' : Fin 2 → A} (h : Pred a s w we)
    (h' : Pred a' s w we') : a = a' ∧ we = we' := by
  obtain ⟨hy, ha⟩ := succOcc_left_unique h.2 h'.2
  refine ⟨ha, funext fun k => ?_⟩
  fin_cases k
  · exact h.1.symm.trans h'.1
  · exact hy

/-- A clause of the split has one prefix variable among its literals of a given
sign. -/
theorem pre_unique {sg : Bool} {t : PTag} {a a' : Bool} {w we we' : Fin 2 → A}
    (h : LitSem sg t (.pre a) w we) (h' : LitSem sg t (.pre a') w we') :
    a = a' ∧ we = we' := by
  cases t <;> cases sg <;>
    first
      | exact h.elim
      | exact pred_unique h h'
      | exact ⟨h.1.trans h'.1.symm, (same_eq h.2.1).trans (same_eq h'.2.1).symm⟩

/-- A code for the literals of a clause, in three values: the variable copy,
the prefix variable occurring positively, the one occurring negatively. -/
def code : PTag → Bool → Fin 3
  | .var, _ => 0
  | _, true => 1
  | _, false => 2

omit [Lax904597.Sat.sat.Structure A] [LinearOrder A] in
theorem code_var (sg : Bool) : code .var sg = 0 := by cases sg <;> rfl

theorem code_pre (a sg : Bool) : code (.pre a) sg = if sg then 1 else 2 := by
  cases sg <;> rfl

theorem lit_eq_of_code {sg sg' : Bool} {t te te' : PTag} {w we we' : Fin 2 → A}
    (h : LitSem sg t te w we) (h' : LitSem sg' t te' w we')
    (hc : code te sg = code te' sg') :
    ((te, we) : PTag × (Fin 2 → A)) = (te', we') ∧ sg = sg' := by
  rcases litSem_tag h with rfl | ⟨a, rfl⟩ <;> rcases litSem_tag h' with rfl | ⟨a', rfl⟩
  · obtain ⟨rfl, rfl⟩ := var_unique h h'
    exact ⟨rfl, rfl⟩
  · rw [code_var, code_pre] at hc
    cases sg' <;> exact absurd hc (by decide)
  · rw [code_var, code_pre] at hc
    cases sg <;> exact absurd hc (by decide)
  · rw [code_pre, code_pre] at hc
    have hsg : sg = sg' := by
      revert hc
      cases sg <;> cases sg' <;> decide
    subst hsg
    obtain ⟨rfl, rfl⟩ := pre_unique h h'
    exact ⟨rfl, rfl⟩

/-- **The split is within the width bound**: a clause has at most three
literals – one variable copy, one prefix variable of each sign. -/
theorem widthAtMostThree_map : Lax799700.ThreeSat.WidthAtMostThree (interp.Map A) := by
  rintro ⟨t, w⟩ x s hocc
  have hl : ∀ i, LitSem (s i) t (x i).1 w (x i).2 := fun i =>
    ((occIn_map_iff t (x i).1 w (x i).2 (s i)).mp (hocc i)).2
  obtain ⟨i, j, hij, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin 4 => code (x i).1 (s i)) (by simp)
  obtain ⟨he, hs⟩ := lit_eq_of_code (hl i) (hl j) hf
  exact ⟨i, j, hij, he, hs⟩

end Width

/-- **Correctness of the interpretation, for counting**: the split has as many
models as the input. -/
theorem sharpThreeSat_map (A : Type) [Lax904597.Sat.sat.Structure A] [LinearOrder A] [Finite A] :
    SharpThreeSAT (interp.Map A) = SharpSAT A := by
  rw [sharpThreeSat_eq_sharpSat widthAtMostThree_map, sharpSat_apply, sharpSat_apply]
  exact (Nat.card_congr (modelEquiv A)).symm

end SharpSatToThreeSat

open SharpSatToThreeSat in
/-- **#SAT reduces parsimoniously to #3SAT**: the clause-splitting
interpretation with determined prefix variables preserves the number of
models. -/
noncomputable def sharpSat_ordered_parsimonious_sharpThreeSat :
    SharpSAT ≤ᵖ[≤] SharpThreeSAT where
  Tag := PTag
  dim := 2
  toInterpretation := interp
  correct A _ _ _ _ := (sharpThreeSat_map A).symm

/-- #3SAT is parsimoniously `#P`-hard. -/
theorem sharpThreeSat_sharpP_parsimoniousHard : SharpP.ParsimoniousHard SharpThreeSAT :=
  SharpP.parsimoniousHard_of_orderedParsimonious sharpSat_ordered_parsimonious_sharpThreeSat
    sharpSat_sharpP_parsimoniousHard

/-- **#3SAT is parsimoniously `#P`-complete.** -/
theorem sharpThreeSat_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpThreeSAT :=
  ⟨sharpThreeSat_mem_sharpP, sharpThreeSat_sharpP_parsimoniousHard⟩

end Lax859101Proofs.DescriptiveComplexity


