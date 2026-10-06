/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.DominatingSet.Counting
import Lax280166Proofs.DescriptiveComplexity.Problems.ExactCover
import Lax280166Proofs.DescriptiveComplexity.Problems.Sat.CountingHardness
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

namespace Lax280166.CountingDominatingSets
end Lax280166.CountingDominatingSets

namespace Lax366625.CountingSat
end Lax366625.CountingSat

namespace Lax799700.CliqueFamily
end Lax799700.CliqueFamily

namespace Lax799700.Common.SatOcc
end Lax799700.Common.SatOcc

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingDominatingSets (DomSetOfSize)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.CliqueFamily (MGAdj MGMarked)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingSat (SatModel SatOccurs)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax799700.CliqueFamily (markedGraph)
end FirstOrder.Language

namespace Lax280166Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (IsCl LitTrue OccIn)
end Lax280166Proofs.DescriptiveComplexity.SatOcc

/-!
# #Dominating Set is parsimoniously `#P`-complete

`DescriptiveComplexity.sharpDominatingSet_sharpP_parsimoniousComplete`, by a reduction
from #SAT (`DescriptiveComplexity.sharpSat_parsimonious_sharpDominatingSet`), order-free.

The reduction of `DescriptiveComplexity.Problems.DominatingSet.Reduction`, from Set
Cover, is not parsimonious, and cannot be made so by adjusting it: a dominating
set may hold element vertices, and a cover smaller than the threshold can be
padded with one. What a count of dominating sets of a given size needs is a
graph in which that size leaves no slack. Here:

* each variable `x` of the formula has two *literal vertices* `(lit true, x)`
  and `(lit false, x)`, adjacent, and two *private vertices* `(priv b, x)`,
  each adjacent to the two literal vertices of `x` and to nothing else;
* each clause `c` has a vertex `(cl, c)`, adjacent to the literal vertices of
  its literals;
* the threshold is the number of variables.

A private vertex is dominated from within the four vertices of its variable, so
a dominating set meets each such group, and at the threshold size it meets each
exactly once and holds nothing else. The one vertex of a group has to dominate
both private vertices, which are not adjacent: it is a literal vertex
(`DescriptiveComplexity.SatToDom.dom_structure`). So the dominating sets of the
threshold size are the assignments of the variables of the formula, and
dominating the clause vertices is satisfying the clauses
(`DescriptiveComplexity.SatToDom.solEquiv`).

Junk – a tagged element that is not a variable, or not a clause – has to be
dominated too, and is made adjacent to every literal vertex. That needs a
literal vertex in the set, which a formula with a clause provides; a formula
with no clause at all has one model, and is sent to the edgeless graph with
everything marked, which has one dominating set of the threshold size
(`DescriptiveComplexity.SatToDom.NoCl`).
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

namespace SatToDom

open Language Structure SatOcc ExactCoverRed

/-- Tags of the reduction. -/
inductive SDTag : Type
  /-- The vertex of the literal of sign `s` of a variable. -/
  | lit (s : Bool)
  /-- One of the two private vertices of a variable. -/
  | priv (b : Bool)
  /-- The vertex of a clause. -/
  | cl
  deriving DecidableEq

instance : Fintype SDTag where
  elems := {.lit true, .lit false, .priv true, .priv false, .cl}
  complete := by
    intro t
    cases t with
    | lit s => cases s <;> decide
    | priv b => cases b <;> decide
    | cl => decide

instance : Nonempty SDTag := ⟨.cl⟩

/-! ### The semantic side -/

section Semantics

variable {A : Type} [Lax904597.Sat.sat.Structure A]

variable (A) in
/-- The formula has no clause at all. -/
def NoCl : Prop := ¬∃ c : A, Lax799700.Common.SatOcc.IsCl c

/-- The vertices the literal vertex `(lit s, x)` is adjacent to: the other
literal vertex of `x`, its private vertices, the clauses the literal occurs in,
and all the junk. -/
def Target (s : Bool) (x : A) : SDTag → A → Prop
  | .lit s', y => (s' ≠ s ∧ y = x) ∨ ¬Lax366625.CountingSat.SatOccurs A y
  | .priv _, y => y = x ∨ ¬Lax366625.CountingSat.SatOccurs A y
  | .cl, y => Lax799700.Common.SatOcc.OccIn y x s ∨ ¬Lax799700.Common.SatOcc.IsCl y

/-- The first vertex is a literal vertex of a variable, adjacent to the
second. -/
def LitDom : SDTag → A → SDTag → A → Prop
  | .lit s, x, t, y => Lax366625.CountingSat.SatOccurs A x ∧ Target s x t y
  | _, _, _, _ => False

/-- The adjacency condition of the interpreted graph. -/
def AdjCore (t₁ : SDTag) (x : A) (t₂ : SDTag) (y : A) : Prop :=
  ¬NoCl A ∧ (LitDom t₁ x t₂ y ∨ LitDom t₂ y t₁ x)

/-- The marking condition of the interpreted graph: one vertex per variable –
or everything, when there is no clause. -/
def MarkedCore (t : SDTag) (x : A) : Prop :=
  NoCl A ∨ (t = .lit true ∧ Lax366625.CountingSat.SatOccurs A x)

theorem litDom_iff {t t' : SDTag} {x y : A} :
    LitDom t x t' y ↔ ∃ s, t = .lit s ∧ Lax366625.CountingSat.SatOccurs A x ∧ Target s x t' y := by
  cases t with
  | lit s =>
    exact ⟨fun h => ⟨s, rfl, h⟩, fun ⟨s', hs, h⟩ => by cases hs; exact h⟩
  | priv b => exact ⟨fun h => (h : False).elim, fun ⟨_, hs, _⟩ => by cases hs⟩
  | cl => exact ⟨fun h => (h : False).elim, fun ⟨_, hs, _⟩ => by cases hs⟩

open Classical in
omit [Lax904597.Sat.sat.Structure A] in
/-- The sign of the true literal of a variable. -/
theorem litTrue_iff_decide {ν : A → Prop} {x : A} {s : Bool} :
    Lax799700.Common.SatOcc.LitTrue ν x s ↔ s = decide (ν x) := by
  by_cases h : ν x <;> cases s <;> simp [Lax799700.Common.SatOcc.LitTrue, h]

end Semantics

/-! ### The formulas and the interpretation -/

section Formulas

variable {α : Type}

/-- `DescriptiveComplexity.SatToDom.NoCl`, as a formula. -/
noncomputable def noClF : Lax904597.Sat.sat.Formula α :=
  ∼((ThreeSatToSat.clF (Sum.inr ())).iExs Unit)

/-- `DescriptiveComplexity.SatToDom.Target`, as a formula. -/
noncomputable def targetF (s : Bool) (x : α) : SDTag → α → Lax904597.Sat.sat.Formula α
  | .lit s', y => (if s' = s then ⊥ else ThreeSatToSat.eqF y x) ⊔ ∼(occursF y)
  | .priv _, y => ThreeSatToSat.eqF y x ⊔ ∼(occursF y)
  | .cl, y => ThreeSatToSat.occF s y x ⊔ ∼(ThreeSatToSat.clF y)

/-- `DescriptiveComplexity.SatToDom.LitDom`, as a formula. -/
noncomputable def litDomF : SDTag → α → SDTag → α → Lax904597.Sat.sat.Formula α
  | .lit s, x, t, y => occursF x ⊓ targetF s x t y
  | _, _, _, _ => ⊥

/-- The adjacency formulas of the interpretation, by tag. -/
noncomputable def adjF (t₁ t₂ : SDTag) : Lax904597.Sat.sat.Formula (Fin 2 × Fin 1) :=
  ∼noClF ⊓ (litDomF t₁ (0, 0) t₂ (1, 0) ⊔ litDomF t₂ (1, 0) t₁ (0, 0))

/-- The mark formulas of the interpretation, by tag. -/
noncomputable def markedF (t : SDTag) : Lax904597.Sat.sat.Formula (Fin 1 × Fin 1) :=
  noClF ⊔ (if t = .lit true then occursF (0, 0) else ⊥)

end Formulas

/-- The interpretation producing, from a CNF structure, the graph whose
dominating sets of the threshold size are its models. -/
noncomputable def sdInterp : Lax904597.Interpretations.FOInterpretation Lax904597.Sat.sat Lax799700.CliqueFamily.markedGraph SDTag 1 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun t => adjF (t 0) (t 1)
    | _, .marked => fun t => markedF (t 0)

/-! ### The points -/

section Points

variable {A : Type}

/-- The vertex of tag `t` over the element `x`. -/
def sdPt (t : SDTag) (x : A) : sdInterp.Map A := (t, fun _ => x)

theorem sdPt_eq_iff {t t' : SDTag} {x x' : A} : sdPt t x = sdPt t' x' ↔ t = t' ∧ x = x' := by
  constructor
  · intro h
    exact ⟨by simpa [sdPt] using congrArg (fun p : sdInterp.Map A => p.1) h,
      by simpa [sdPt] using congrArg (fun p : sdInterp.Map A => p.2 0) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem sdPt_surj (q : sdInterp.Map A) : ∃ t x, q = sdPt t x :=
  ⟨q.1, q.2 0, Prod.ext_iff.mpr ⟨rfl, funext fun i => congrArg q.2 (Subsingleton.elim i 0)⟩⟩

end Points

/-! ### Characterization of the two relations -/

section Characterizations

variable {A : Type} [Lax904597.Sat.sat.Structure A]

section Realize

variable {α : Type} {v : α → A}

theorem realize_noClF : (noClF (α := α)).Realize v ↔ NoCl A := by
  simp only [noClF, Formula.realize_not, Formula.realize_iExs, ThreeSatToSat.realize_clF,
    Sum.elim_inr, NoCl]
  exact not_congr ⟨fun ⟨i, h⟩ => ⟨i (), h⟩, fun ⟨c, h⟩ => ⟨fun _ => c, h⟩⟩

theorem realize_targetF {s : Bool} {x y : α} {t : SDTag} :
    (targetF s x t y).Realize v ↔ Target s (v x) t (v y) := by
  cases t with
  | lit s' =>
    by_cases h : s' = s <;>
      simp [targetF, Target, h, realize_occursF, ThreeSatToSat.realize_eqF]
  | priv b => simp [targetF, Target, realize_occursF, ThreeSatToSat.realize_eqF]
  | cl => simp [targetF, Target, ThreeSatToSat.realize_clF]

theorem realize_litDomF {t₁ t₂ : SDTag} {x y : α} :
    (litDomF t₁ x t₂ y).Realize v ↔ LitDom t₁ (v x) t₂ (v y) := by
  cases t₁ <;> simp [litDomF, LitDom, realize_targetF, realize_occursF]

end Realize

theorem realize_adjF {t₁ t₂ : SDTag} {v : Fin 2 × Fin 1 → A} :
    (adjF t₁ t₂).Realize v ↔ AdjCore t₁ (v (0, 0)) t₂ (v (1, 0)) := by
  simp [adjF, AdjCore, realize_noClF, realize_litDomF]

theorem realize_markedF {t : SDTag} {v : Fin 1 × Fin 1 → A} :
    (markedF t).Realize v ↔ MarkedCore t (v (0, 0)) := by
  by_cases h : t = .lit true <;>
    simp [markedF, MarkedCore, h, realize_noClF, realize_occursF]

theorem mgAdj_pt {t₁ t₂ : SDTag} {x y : A} :
    Lax799700.CliqueFamily.MGAdj (sdPt t₁ x) (sdPt t₂ y) ↔ AdjCore t₁ x t₂ y := by
  rw [Lax799700.CliqueFamily.MGAdj, sdPt, sdPt, FOInterpretation.relMap_map]
  exact realize_adjF

theorem mgMarked_pt {t : SDTag} {x : A} : Lax799700.CliqueFamily.MGMarked (sdPt t x) ↔ MarkedCore t x := by
  rw [Lax799700.CliqueFamily.MGMarked, sdPt, FOInterpretation.relMap_map]
  exact realize_markedF

end Characterizations

/-! ### The two sides of the bijection -/

section Sets

variable {A : Type} [Lax904597.Sat.sat.Structure A]

/-- The dominating set of an assignment: the vertices of its true literals – or
everything, when there is no clause. -/
def domOf (ν : A → Prop) (p : sdInterp.Map A) : Prop :=
  NoCl A ∨ ∃ s x, p = sdPt (.lit s) x ∧ Lax366625.CountingSat.SatOccurs A x ∧ Lax799700.Common.SatOcc.LitTrue ν x s

/-- The assignment of a dominating set: the variables whose positive literal
vertex it holds. -/
def modelOf (D : sdInterp.Map A → Prop) (x : A) : Prop :=
  D (sdPt (.lit true) x) ∧ Lax366625.CountingSat.SatOccurs A x

/-- The marked vertices, one per variable. -/
def markEnum (x : {x : A // Lax366625.CountingSat.SatOccurs A x}) : sdInterp.Map A := sdPt (.lit true) x.1

open Classical in
/-- The vertices of the dominating set of an assignment, one per variable. -/
noncomputable def chosenEnum (ν : A → Prop) (x : {x : A // Lax366625.CountingSat.SatOccurs A x}) :
    sdInterp.Map A :=
  sdPt (.lit (decide (ν x.1))) x.1

theorem markEnum_injective : Function.Injective (markEnum (A := A)) :=
  fun _ _ h => Subtype.ext (sdPt_eq_iff.mp h).2

theorem chosenEnum_injective (ν : A → Prop) : Function.Injective (chosenEnum ν) :=
  fun _ _ h => Subtype.ext (sdPt_eq_iff.mp h).2

theorem range_markEnum (hne : ¬NoCl A) :
    Set.range (markEnum (A := A)) = {p | Lax799700.CliqueFamily.MGMarked p} := by
  ext p
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, rfl⟩
    exact mgMarked_pt.mpr (Or.inr ⟨rfl, x.2⟩)
  · intro hp
    obtain ⟨t, x, rfl⟩ := sdPt_surj p
    rcases mgMarked_pt.mp hp with h | ⟨ht, hx⟩
    · exact absurd h hne
    · subst ht
      exact ⟨⟨x, hx⟩, rfl⟩

theorem range_chosenEnum (hne : ¬NoCl A) (ν : A → Prop) :
    Set.range (chosenEnum ν) = {p | domOf ν p} := by
  ext p
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, rfl⟩
    exact Or.inr ⟨_, x.1, rfl, x.2, litTrue_iff_decide.mpr rfl⟩
  · rintro (h | ⟨s, x, rfl, hx, hT⟩)
    · exact absurd h hne
    · refine ⟨⟨x, hx⟩, ?_⟩
      rw [litTrue_iff_decide.mp hT]
      rfl

theorem ncard_marked (hne : ¬NoCl A) :
    {p : sdInterp.Map A | Lax799700.CliqueFamily.MGMarked p}.ncard = Nat.card {x : A // Lax366625.CountingSat.SatOccurs A x} := by
  rw [← range_markEnum hne]
  exact Set.ncard_range_of_injective markEnum_injective

theorem ncard_domOf (hne : ¬NoCl A) (ν : A → Prop) :
    {p | domOf ν p}.ncard = Nat.card {x : A // Lax366625.CountingSat.SatOccurs A x} := by
  rw [← range_chosenEnum hne ν]
  exact Set.ncard_range_of_injective (chosenEnum_injective ν)

/-! ### Correctness -/

/-- The dominating set of a model is one, of the threshold size. -/
theorem domSetOfSize_domOf [Finite A] {ν : A → Prop} (hν : Lax366625.CountingSat.SatModel A ν) :
    Lax280166.CountingDominatingSets.DomSetOfSize (sdInterp.Map A) (domOf ν) := by
  by_cases hne : NoCl A
  · refine ⟨sdInterp.map_finite A, fun v => Or.inl (Or.inl hne), ?_⟩
    exact congrArg Set.ncard (Set.ext fun p => by
      obtain ⟨t, x, rfl⟩ := sdPt_surj p
      exact ⟨fun _ => mgMarked_pt.mpr (Or.inl hne), fun _ => Or.inl hne⟩)
  · refine ⟨sdInterp.map_finite A, fun q => ?_,
      (ncard_domOf hne ν).trans (ncard_marked hne).symm⟩
    obtain ⟨t, y, rfl⟩ := sdPt_surj q
    obtain ⟨x₀, s₀, hx₀, hT₀⟩ : ∃ x s, Lax366625.CountingSat.SatOccurs A x ∧ Lax799700.Common.SatOcc.LitTrue ν x s := by
      obtain ⟨c, hc⟩ := not_not.mp hne
      obtain ⟨x, ⟨hp, hx⟩ | ⟨hn, hx⟩⟩ := hν.1 c hc
      · exact ⟨x, true, ⟨c, hc, Or.inl hp⟩, hx⟩
      · exact ⟨x, false, ⟨c, hc, Or.inr hn⟩, hx⟩
    have key : ∀ (x : A) (s : Bool), Lax366625.CountingSat.SatOccurs A x → Lax799700.Common.SatOcc.LitTrue ν x s → Target s x t y →
        ∃ u, domOf ν u ∧ Lax799700.CliqueFamily.MGAdj u (sdPt t y) := fun x s hx hT htar =>
      ⟨sdPt (.lit s) x, Or.inr ⟨s, x, rfl, hx, hT⟩, mgAdj_pt.mpr ⟨hne, Or.inl ⟨hx, htar⟩⟩⟩
    cases t with
    | lit s =>
      by_cases hy : Lax366625.CountingSat.SatOccurs A y
      · by_cases hT : Lax799700.Common.SatOcc.LitTrue ν y s
        · exact Or.inl (Or.inr ⟨s, y, rfl, hy, hT⟩)
        · exact Or.inr (key y (!s) hy (litTrue_not.mpr hT)
            (Or.inl ⟨by cases s <;> decide, rfl⟩))
      · exact Or.inr (key x₀ s₀ hx₀ hT₀ (Or.inr hy))
    | priv b =>
      by_cases hy : Lax366625.CountingSat.SatOccurs A y
      · by_cases hνy : ν y
        · exact Or.inr (key y true hy hνy (Or.inl rfl))
        · exact Or.inr (key y false hy hνy (Or.inl rfl))
      · exact Or.inr (key x₀ s₀ hx₀ hT₀ (Or.inr hy))
    | cl =>
      by_cases hy : Lax799700.Common.SatOcc.IsCl y
      · obtain ⟨x, ⟨hp, hx⟩ | ⟨hn, hx⟩⟩ := hν.1 y hy
        · exact Or.inr (key x true ⟨y, hy, Or.inl hp⟩ hx (Or.inl ⟨hy, hp⟩))
        · exact Or.inr (key x false ⟨y, hy, Or.inr hn⟩ hx (Or.inl ⟨hy, hn⟩))
      · exact Or.inr (key x₀ s₀ hx₀ hT₀ (Or.inr hy))

/-- **A dominating set of the threshold size is an assignment**: it consists of
literal vertices of variables, one per variable. -/
theorem dom_structure [Finite A] (hne : ¬NoCl A) {D : sdInterp.Map A → Prop}
    (hD : Lax280166.CountingDominatingSets.DomSetOfSize (sdInterp.Map A) D) :
    (∀ t x, D (sdPt t x) → ∃ s, t = .lit s ∧ Lax366625.CountingSat.SatOccurs A x) ∧
      (∀ x, Lax366625.CountingSat.SatOccurs A x → ∃ s, D (sdPt (.lit s) x)) ∧
      ∀ t t' x, D (sdPt t x) → D (sdPt t' x) → t = t' := by
  obtain ⟨hfin, hdom, hcard⟩ := hD
  have hpriv : ∀ (b : Bool) (x : A), Lax366625.CountingSat.SatOccurs A x →
      ∃ t, D (sdPt t x) ∧ (t = .priv b ∨ ∃ s, t = .lit s) := by
    intro b x hx
    rcases hdom (sdPt (.priv b) x) with h | ⟨u, hu, hadj⟩
    · exact ⟨_, h, Or.inl rfl⟩
    · obtain ⟨t, x', rfl⟩ := sdPt_surj u
      obtain ⟨-, h | h⟩ := mgAdj_pt.mp hadj
      · obtain ⟨s, rfl, -, htar⟩ := litDom_iff.mp h
        rcases htar with hxx | hno
        · rw [hxx]
          exact ⟨_, hu, Or.inr ⟨s, rfl⟩⟩
        · exact absurd hx hno
      · obtain ⟨s, hs, -⟩ := litDom_iff.mp h
        cases hs
  have hex : ∀ x : {x : A // Lax366625.CountingSat.SatOccurs A x}, ∃ p : {p // D p}, ∃ t, p.1 = sdPt t x.1 :=
    fun x => by
      obtain ⟨t, ht, -⟩ := hpriv true x.1 x.2
      exact ⟨⟨_, ht⟩, t, rfl⟩
  choose g hg using hex
  have hinj : Function.Injective g := by
    intro a b hab
    obtain ⟨t, ht⟩ := hg a
    obtain ⟨t', ht'⟩ := hg b
    rw [hab] at ht
    exact Subtype.ext (sdPt_eq_iff.mp (ht.symm.trans ht')).2
  have hcardD : Nat.card {p // D p} = Nat.card {x : A // Lax366625.CountingSat.SatOccurs A x} :=
    (Nat.card_coe_set_eq {p | D p}).trans (hcard.trans (ncard_marked hne))
  have hsurj := (hinj.bijective_of_nat_card_le hcardD.le).2
  have huniq : ∀ t t' x, D (sdPt t x) → D (sdPt t' x) → t = t' ∧ Lax366625.CountingSat.SatOccurs A x := by
    intro t t' x h h'
    obtain ⟨a, ha⟩ := hsurj ⟨_, h⟩
    obtain ⟨b, hb⟩ := hsurj ⟨_, h'⟩
    obtain ⟨t₁, ht₁⟩ := hg a
    obtain ⟨t₂, ht₂⟩ := hg b
    rw [ha] at ht₁
    rw [hb] at ht₂
    have hax : x = a.1 := (sdPt_eq_iff.mp ht₁).2
    have hbx : x = b.1 := (sdPt_eq_iff.mp ht₂).2
    have hocc : Lax366625.CountingSat.SatOccurs A x := by
      rw [hax]
      exact a.2
    have hab : a = b := Subtype.ext (hax.symm.trans hbx)
    rw [hab] at ha
    exact ⟨(sdPt_eq_iff.mp (congrArg Subtype.val (ha.symm.trans hb))).1, hocc⟩
  have hlit : ∀ x, Lax366625.CountingSat.SatOccurs A x → ∃ s, D (sdPt (.lit s) x) := by
    intro x hx
    obtain ⟨t, ht, hcase⟩ := hpriv true x hx
    obtain ⟨t', ht', hcase'⟩ := hpriv false x hx
    rcases hcase with rfl | ⟨s, rfl⟩
    · rcases hcase' with rfl | ⟨s, rfl⟩
      · exact absurd (huniq _ _ x ht ht').1 (by decide)
      · exact ⟨s, ht'⟩
    · exact ⟨s, ht⟩
  refine ⟨fun t x h => ?_, hlit, fun t t' x h h' => (huniq t t' x h h').1⟩
  have hocc := (huniq t t x h h).2
  obtain ⟨s, hs⟩ := hlit x hocc
  exact ⟨s, (huniq _ _ x h hs).1, hocc⟩

/-- The assignment of a dominating set of the threshold size is a model. -/
theorem satModel_modelOf [Finite A] {D : sdInterp.Map A → Prop}
    (hD : Lax280166.CountingDominatingSets.DomSetOfSize (sdInterp.Map A) D) : Lax366625.CountingSat.SatModel A (modelOf D) := by
  refine ⟨fun c hc => ?_, fun x hx => hx.2⟩
  have hne : ¬NoCl A := fun h => h ⟨c, hc⟩
  obtain ⟨hlitonly, -, huniq⟩ := dom_structure hne hD
  rcases hD.2.1 (sdPt .cl c) with h | ⟨u, hu, hadj⟩
  · obtain ⟨s, hs, -⟩ := hlitonly _ _ h
    cases hs
  · obtain ⟨t, x, rfl⟩ := sdPt_surj u
    obtain ⟨-, h | h⟩ := mgAdj_pt.mp hadj
    · obtain ⟨s, rfl, hx, htar⟩ := litDom_iff.mp h
      rcases htar with ho | hno
      · cases s
        · exact ⟨x, Or.inr ⟨ho.2, fun hm => absurd (huniq _ _ x hm.1 hu) (by decide)⟩⟩
        · exact ⟨x, Or.inl ⟨ho.2, hu, hx⟩⟩
      · exact absurd hc hno
    · obtain ⟨s, hs, -⟩ := litDom_iff.mp h
      cases hs

/-- A dominating set of the threshold size is the dominating set of its
assignment. -/
theorem domOf_modelOf [Finite A] {D : sdInterp.Map A → Prop}
    (hD : Lax280166.CountingDominatingSets.DomSetOfSize (sdInterp.Map A) D) : domOf (modelOf D) = D := by
  funext p
  apply propext
  obtain ⟨t, x, rfl⟩ := sdPt_surj p
  by_cases hne : NoCl A
  · have := hD.1
    have hmk : {q : sdInterp.Map A | Lax799700.CliqueFamily.MGMarked q} = Set.univ :=
      Set.eq_univ_of_forall fun q => by
        obtain ⟨t', x', rfl⟩ := sdPt_surj q
        exact mgMarked_pt.mpr (Or.inl hne)
    have heq := Set.eq_of_subset_of_ncard_le (Set.subset_univ {q | D q})
      (by rw [hD.2.2, hmk])
    exact ⟨fun _ => (Set.ext_iff.mp heq _).mpr trivial, fun _ => Or.inl hne⟩
  · obtain ⟨hlitonly, hlit, huniq⟩ := dom_structure hne hD
    constructor
    · rintro (h | ⟨s, x', heq, hx, hT⟩)
      · exact absurd h hne
      · obtain ⟨ht, hxx⟩ := sdPt_eq_iff.mp heq
        subst ht hxx
        obtain ⟨s', hs'⟩ := hlit x hx
        cases s <;> cases s'
        exacts [hs', absurd ⟨hs', hx⟩ hT, hT.1, hT.1]
    · intro h
      obtain ⟨s, rfl, hx⟩ := hlitonly _ _ h
      refine Or.inr ⟨s, x, rfl, hx, ?_⟩
      cases s
      · exact fun hm => absurd (huniq _ _ x hm.1 h) (by decide)
      · exact ⟨h, hx⟩

/-- A model is the assignment of its dominating set. -/
theorem modelOf_domOf {ν : A → Prop} (hν : Lax366625.CountingSat.SatModel A ν) : modelOf (domOf ν) = ν := by
  funext x
  apply propext
  constructor
  · rintro ⟨h | ⟨s, x', heq, -, hT⟩, hocc⟩
    · obtain ⟨c, hc, -⟩ := hocc
      exact absurd ⟨c, hc⟩ h
    · obtain ⟨hs, hx⟩ := sdPt_eq_iff.mp heq
      cases hs
      rw [hx]
      exact hT
  · intro hx
    have hocc := hν.2 x hx
    refine ⟨?_, hocc⟩
    by_cases hne : NoCl A
    exacts [Or.inl hne, Or.inr ⟨true, x, rfl, hocc, hx⟩]

variable (A) [Finite A]

/-- **The dominating sets of the threshold size of the interpreted graph are
the models of the CNF formula**, bijectively. -/
def solEquiv :
    {ν : A → Prop // Lax366625.CountingSat.SatModel A ν} ≃
      {D : sdInterp.Map A → Prop // Lax280166.CountingDominatingSets.DomSetOfSize (sdInterp.Map A) D} where
  toFun ν := ⟨domOf ν.1, domSetOfSize_domOf ν.2⟩
  invFun D := ⟨modelOf D.1, satModel_modelOf D.2⟩
  left_inv ν := Subtype.ext (modelOf_domOf ν.2)
  right_inv D := Subtype.ext (domOf_modelOf D.2)

end Sets

end SatToDom

open SatToDom in
/-- **#SAT reduces parsimoniously to #Dominating Set**, without an order. -/
noncomputable def sharpSat_parsimonious_sharpDominatingSet :
    SharpSAT ≤ᵖ SharpDominatingSet where
  Tag := SDTag
  dim := 1
  toInterpretation := sdInterp
  correct A _ _ _ := Nat.card_congr (solEquiv A)

/-- #Dominating Set is parsimoniously `#P`-hard. -/
theorem sharpDominatingSet_sharpP_parsimoniousHard :
    SharpP.ParsimoniousHard SharpDominatingSet :=
  SharpP.parsimoniousHard_of_parsimonious sharpSat_parsimonious_sharpDominatingSet
    sharpSat_sharpP_parsimoniousHard

/-- **#Dominating Set is parsimoniously `#P`-complete**, counting the dominating
sets of exactly the threshold size. -/
theorem sharpDominatingSet_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpDominatingSet :=
  ⟨sharpDominatingSet_mem_sharpP, sharpDominatingSet_sharpP_parsimoniousHard⟩

end Lax280166Proofs.DescriptiveComplexity


