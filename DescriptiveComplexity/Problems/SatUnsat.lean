/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Sat
import DescriptiveComplexity.Difference

/-!
# SAT-UNSAT, the canonical DP problem

**SAT-UNSAT** ([Papadimitriou & Yannakakis 1984][papadimitriou1984complexity]):
given *two* CNF formulas, is the first satisfiable *and* the second not? It is
the prototypical problem of `DescriptiveComplexity.DP`, the class of differences of
NP problems, and it wears its DP definition on its sleeve – one half is an NP
condition, the other a coNP one, and they are imposed on disjoint parts of the
vocabulary.

## The vocabulary

An instance carries the two formulas side by side: `Language.satPair` is two
copies of `Language.sat`, one per side. Both live on the same universe – there
is no need to keep the two formulas' variables apart, since each side's clauses
only mention their own occurrence relations, and a truth assignment for one
side is free to do as it likes on the other side's variables.

## What is here, and what is not

The vocabulary, the semantics and isomorphism-invariance, and the three
problems: `DescriptiveComplexity.SATUNSAT` itself together with its two halves
`DescriptiveComplexity.SatFirst` (an NP condition) and
`DescriptiveComplexity.UnsatSecond` (a coNP one), which are what a DP definition of
it will conjoin. Satisfiability of a side is stated once, parameterized by the
triple of relation symbols to read (`DescriptiveComplexity.SatWith`), since the two
sides differ only in that.

**Membership in DP** (`DescriptiveComplexity.satUnsat_mem_DP`) is proved without
writing a single new kernel: each side is *projected* onto a plain
`Language.sat` instance by a one-dimensional, single-tag interpretation
(`DescriptiveComplexity.sideInterp`), so `SatFirst` reduces to SAT and `SatSecond`
does too; `Σ₁`-definability of the first half and `Π₁`-definability of the
second then come from `DescriptiveComplexity.sat_sigmaSODefinable` by closure of the
levels under FO reductions, the second after complementing the reduction.

**DP-hardness** is in `DescriptiveComplexity.Problems.SatUnsat.Hardness`
(`DescriptiveComplexity.satUnsat_hard_of_dpDefinable`, whence
`DescriptiveComplexity.SATUNSAT_DP_complete`): the Cook–Levin discharge of the `Σ₁`
half and that of the complement of the `Π₁` half, run side by side into a
single paired instance. The lemma below on satisfiability along a
clause-covering embedding is the step it needs.
-/

namespace FirstOrder

namespace Language

/-- Relation symbols of the language of *pairs* of CNF instances: two copies of
`Language.satRel`, one per side. -/
inductive satPairRel : ℕ → Type
  /-- `isClause₁ c`: `c` is a clause of the first formula. -/
  | isClause₁ : satPairRel 1
  /-- `posIn₁ c x`: `x` occurs positively in the first formula's clause `c`. -/
  | posIn₁ : satPairRel 2
  /-- `negIn₁ c x`: `x` occurs negatively in the first formula's clause `c`. -/
  | negIn₁ : satPairRel 2
  /-- `isClause₂ c`: `c` is a clause of the second formula. -/
  | isClause₂ : satPairRel 1
  /-- `posIn₂ c x`: `x` occurs positively in the second formula's clause `c`. -/
  | posIn₂ : satPairRel 2
  /-- `negIn₂ c x`: `x` occurs negatively in the second formula's clause `c`. -/
  | negIn₂ : satPairRel 2
  deriving DecidableEq

/-- The relational vocabulary of pairs of CNF instances. -/
protected def satPair : Language :=
  ⟨fun _ => Empty, satPairRel⟩
  deriving IsRelational

/-- “Is a clause of the first formula”. -/
abbrev spIsCl₁ : Language.satPair.Relations 1 := .isClause₁

/-- “Occurs positively in”, first formula. -/
abbrev spPos₁ : Language.satPair.Relations 2 := .posIn₁

/-- “Occurs negatively in”, first formula. -/
abbrev spNeg₁ : Language.satPair.Relations 2 := .negIn₁

/-- “Is a clause of the second formula”. -/
abbrev spIsCl₂ : Language.satPair.Relations 1 := .isClause₂

/-- “Occurs positively in”, second formula. -/
abbrev spPos₂ : Language.satPair.Relations 2 := .posIn₂

/-- “Occurs negatively in”, second formula. -/
abbrev spNeg₂ : Language.satPair.Relations 2 := .negIn₂

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Satisfiability of one side -/

section Defs

variable (A : Type) [Language.satPair.Structure A]

/-- Satisfiability of the side of the instance read by the given triple of
symbols: some assignment of truth values makes every clause of that side
contain a true literal. Both sides of `SAT-UNSAT` are instances of this. -/
def SatWith (isCl : Language.satPair.Relations 1)
    (pos neg : Language.satPair.Relations 2) : Prop :=
  ∃ ν : A → Prop, ∀ c : A, RelMap isCl ![c] →
    ∃ x : A, (RelMap pos ![c, x] ∧ ν x) ∨ (RelMap neg ![c, x] ∧ ¬ν x)

end Defs

section Iso

variable {A B : Type} [Language.satPair.Structure A] [Language.satPair.Structure B]

private theorem satWith_of_iso (e : A ≃[Language.satPair] B)
    (isCl : Language.satPair.Relations 1) (pos neg : Language.satPair.Relations 2)
    (h : SatWith A isCl pos neg) : SatWith B isCl pos neg := by
  obtain ⟨ν, hν⟩ := h
  refine ⟨fun b => ν (e.symm b), fun c hc => ?_⟩
  obtain ⟨x, hx⟩ := hν (e.symm c) ((relMap_equiv₁ e.symm isCl c).mp hc)
  refine ⟨e x, ?_⟩
  rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
  · refine Or.inl ⟨?_, by simpa using hT⟩
    simpa using (relMap_equiv₂ e pos (e.symm c) x).mp hp
  · refine Or.inr ⟨?_, by simpa using hT⟩
    simpa using (relMap_equiv₂ e neg (e.symm c) x).mp hn

/-- Satisfiability of a side is isomorphism-invariant. -/
theorem satWith_iso (e : A ≃[Language.satPair] B) (isCl : Language.satPair.Relations 1)
    (pos neg : Language.satPair.Relations 2) :
    SatWith A isCl pos neg ↔ SatWith B isCl pos neg :=
  ⟨satWith_of_iso e isCl pos neg, satWith_of_iso e.symm isCl pos neg⟩

end Iso

/-- The first formula of the pair is satisfiable: the NP half of SAT-UNSAT. -/
def SatFirst : DecisionProblem Language.satPair where
  Holds := fun A inst => @SatWith A inst spIsCl₁ spPos₁ spNeg₁
  iso_invariant := fun e => satWith_iso e _ _ _

/-- The second formula of the pair is unsatisfiable: the coNP half. -/
def UnsatSecond : DecisionProblem Language.satPair where
  Holds := fun A inst => ¬@SatWith A inst spIsCl₂ spPos₂ spNeg₂
  iso_invariant := fun e => not_congr (satWith_iso e _ _ _)

/-- **SAT-UNSAT**: the first formula of the pair is satisfiable and the second
is not. -/
def SATUNSAT : DecisionProblem Language.satPair where
  Holds := fun A inst =>
    @SatWith A inst spIsCl₁ spPos₁ spNeg₁ ∧ ¬@SatWith A inst spIsCl₂ spPos₂ spNeg₂
  iso_invariant := fun e =>
    and_congr (satWith_iso e _ _ _) (not_congr (satWith_iso e _ _ _))

/-! ### Reading one side as a plain CNF instance

Rather than restate SAT's `Σ₁` kernel for a pair of formulas, each side is
*projected* onto a plain `Language.sat` instance by a one-dimensional,
single-tag interpretation. Definability of both halves is then inherited from
`DescriptiveComplexity.sat_sigmaSODefinable` by closure under FO reductions – no new
kernel, and no second copy of its realization proof. -/

section Projection

/-- The interpretation reading the side given by a triple of symbols as a
plain CNF instance: same universe, the three relations renamed. -/
def sideInterp (isCl : Language.satPair.Relations 1)
    (pos neg : Language.satPair.Relations 2) :
    FOInterpretation Language.satPair Language.sat Unit 1 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun _ => Relations.formula₁ isCl (Term.var (0, 0))
    | _, .posIn => fun _ => Relations.formula₂ pos (Term.var (0, 0)) (Term.var (1, 0))
    | _, .negIn => fun _ => Relations.formula₂ neg (Term.var (0, 0)) (Term.var (1, 0))

variable {A : Type} [Language.satPair.Structure A]
variable (isCl : Language.satPair.Relations 1) (pos neg : Language.satPair.Relations 2)

@[simp]
theorem sideInterp_isClause (w : Fin 1 → A) :
    RelMap (M := (sideInterp isCl pos neg).Map A) satIsClause ![((), w)] ↔
      RelMap isCl ![w 0] := by
  rw [FOInterpretation.relMap_map]
  exact Formula.realize_rel₁

@[simp]
theorem sideInterp_posIn (w w' : Fin 1 → A) :
    RelMap (M := (sideInterp isCl pos neg).Map A) satPosIn ![((), w), ((), w')] ↔
      RelMap pos ![w 0, w' 0] := by
  rw [FOInterpretation.relMap_map]
  exact Formula.realize_rel₂

@[simp]
theorem sideInterp_negIn (w w' : Fin 1 → A) :
    RelMap (M := (sideInterp isCl pos neg).Map A) satNegIn ![((), w), ((), w')] ↔
      RelMap neg ![w 0, w' 0] := by
  rw [FOInterpretation.relMap_map]
  exact Formula.realize_rel₂

/-- The projected instance is satisfiable exactly when that side is. -/
theorem satisfiable_sideInterp :
    Satisfiable ((sideInterp isCl pos neg).Map A) ↔ SatWith A isCl pos neg := by
  constructor
  · rintro ⟨ν, hν⟩
    refine ⟨fun a => ν ((), fun _ => a), fun c hc => ?_⟩
    obtain ⟨x, hx⟩ := hν ((), fun _ => c) ((sideInterp_isClause isCl pos neg _).mpr hc)
    obtain ⟨⟨⟩, w⟩ := x
    have hw : (fun _ : Fin 1 => w 0) = w := funext fun j => congrArg w (Subsingleton.elim 0 j)
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact ⟨w 0, Or.inl ⟨(sideInterp_posIn isCl pos neg _ _).mp hp, by
        change ν ((), fun _ => w 0); rw [hw]; exact hT⟩⟩
    · exact ⟨w 0, Or.inr ⟨(sideInterp_negIn isCl pos neg _ _).mp hn, by
        change ¬ν ((), fun _ => w 0); rw [hw]; exact hT⟩⟩
  · rintro ⟨ν, hν⟩
    refine ⟨fun p => ν (p.2 0), ?_⟩
    rintro ⟨⟨⟩, w⟩ hc
    obtain ⟨x, hx⟩ := hν (w 0) ((sideInterp_isClause isCl pos neg w).mp hc)
    refine ⟨((), fun _ => x), ?_⟩
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact Or.inl ⟨(sideInterp_posIn isCl pos neg w _).mpr hp, hT⟩
    · exact Or.inr ⟨(sideInterp_negIn isCl pos neg w _).mpr hn, hT⟩

end Projection

/-! ### Satisfiability ignores elements outside the formula

The step both halves of a DP-hardness pairing will need. Pairing two
reductions into one instance forces a common dimension and a common universe,
so each side's formula ends up sitting inside a larger structure: the other
side's points are there too, and so are the tuples the shorter side does not
use. Those extra elements are *not* harmless by fiat – see the padding warning
in `ROADMAP.md` – but they are harmless once they are neither clauses nor
occurrences, which is what the lemma below says.

It is stated as transfer along an injection `j` that reflects the three
relations, hits every clause, and hits every element occurring in a clause of
its image. Elements outside the image are then pure spectators: a truth
assignment may do as it likes on them. -/

section Cover

variable {A B : Type} [Language.sat.Structure A] [Language.sat.Structure B]

/-- **Satisfiability transfers along a clause-covering embedding.** The extra
elements of `A` – those outside the image of `j` – are neither clauses nor
occurrences, so they constrain nothing and a satisfying assignment of `B`
extends to them arbitrarily. -/
theorem satisfiable_iff_of_cover (j : B → A) (hj : Function.Injective j)
    (hcl : ∀ b : B, RelMap satIsClause ![j b] ↔ RelMap satIsClause ![b])
    (hpos : ∀ b b' : B, RelMap satPosIn ![j b, j b'] ↔ RelMap satPosIn ![b, b'])
    (hneg : ∀ b b' : B, RelMap satNegIn ![j b, j b'] ↔ RelMap satNegIn ![b, b'])
    (hclImg : ∀ c : A, RelMap satIsClause ![c] → ∃ b : B, c = j b)
    (hoccImg : ∀ (b : B) (x : A),
      RelMap satPosIn ![j b, x] ∨ RelMap satNegIn ![j b, x] → ∃ b' : B, x = j b') :
    Satisfiable A ↔ Satisfiable B := by
  constructor
  · rintro ⟨ν, hν⟩
    refine ⟨fun b => ν (j b), fun c hc => ?_⟩
    obtain ⟨x, hx⟩ := hν (j c) ((hcl c).mpr hc)
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · obtain ⟨c', rfl⟩ := hoccImg c x (Or.inl hp)
      exact ⟨c', Or.inl ⟨(hpos c c').mp hp, hT⟩⟩
    · obtain ⟨c', rfl⟩ := hoccImg c x (Or.inr hn)
      exact ⟨c', Or.inr ⟨(hneg c c').mp hn, hT⟩⟩
  · rintro ⟨ν, hν⟩
    refine ⟨fun a => ∃ b : B, a = j b ∧ ν b, fun c hc => ?_⟩
    have himg : ∀ b : B, (∃ b' : B, j b = j b' ∧ ν b') ↔ ν b := by
      refine fun b => ⟨?_, fun h => ⟨b, rfl, h⟩⟩
      rintro ⟨b', hb', hν'⟩
      exact hj hb' ▸ hν'
    obtain ⟨c', rfl⟩ := hclImg c hc
    obtain ⟨x, hx⟩ := hν c' ((hcl c').mp hc)
    refine ⟨j x, ?_⟩
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact Or.inl ⟨(hpos c' x).mpr hp, (himg x).mpr hT⟩
    · exact Or.inr ⟨(hneg c' x).mpr hn, fun h => hT ((himg x).mp h)⟩

end Cover

/-! ### Membership in DP -/

/-- The second formula of the pair is satisfiable: the problem
`DescriptiveComplexity.UnsatSecond` complements. -/
def SatSecond : DecisionProblem Language.satPair where
  Holds := fun A inst => @SatWith A inst spIsCl₂ spPos₂ spNeg₂
  iso_invariant := fun e => satWith_iso e _ _ _

/-- Projecting the first side is a reduction of `SatFirst` to SAT. -/
def satFirst_le_sat : SatFirst ≤ᶠᵒ SAT where
  Tag := Unit
  dim := 1
  toInterpretation := sideInterp spIsCl₁ spPos₁ spNeg₁
  correct _ _ _ := (satisfiable_sideInterp spIsCl₁ spPos₁ spNeg₁).symm

/-- Projecting the second side is a reduction of `SatSecond` to SAT. -/
def satSecond_le_sat : SatSecond ≤ᶠᵒ SAT where
  Tag := Unit
  dim := 1
  toInterpretation := sideInterp spIsCl₂ spPos₂ spNeg₂
  correct _ _ _ := (satisfiable_sideInterp spIsCl₂ spPos₂ spNeg₂).symm

/-- **The first side's satisfiability is `Σ₁`-definable**, inherited from SAT
along the projection. -/
theorem satFirst_sigmaSODefinable : SigmaSODefinable 1 SatFirst :=
  sat_sigmaSODefinable.of_foReduction satFirst_le_sat

/-- `UnsatSecond` is the complement of `SatSecond`. -/
theorem unsatSecond_eq_compl : UnsatSecond = SatSecondᶜ :=
  DecisionProblem.ext fun _ _ => Iff.rfl

/-- **The second side's unsatisfiability is `Π₁`-definable**: the complement of
an NP condition, the reduction complementing along with it. -/
theorem unsatSecond_piSODefinable : PiSODefinable 1 UnsatSecond := by
  rw [unsatSecond_eq_compl]
  exact PiSODefinable.of_foReduction satSecond_le_sat.compl
    ((compl_mem_coNP_iff SAT).mpr sat_sigmaSODefinable)

/-- **SAT-UNSAT is in DP**, by its very shape: an NP condition on one side and
a coNP condition on the other, imposed together. -/
theorem satUnsat_mem_DP : SATUNSAT ∈ DP :=
  ⟨SatFirst, UnsatSecond, satFirst_sigmaSODefinable, unsatSecond_piSODefinable,
    fun _ _ _ _ => Iff.rfl⟩

end DescriptiveComplexity
