/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax859101Proofs.DescriptiveComplexity.OccurrenceOrder
import Lax859101Proofs.DescriptiveComplexity.Problems.Sat.Counting
import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
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

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax859101Proofs.DescriptiveComplexity
export Lax366625.CountingSat (SatModel SatOccurs)
end Lax859101Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat)
end FirstOrder.Language

namespace Lax859101Proofs.DescriptiveComplexity.SatOcc
export Lax799700.Common.SatOcc (LitTrue OccIn)
end Lax859101Proofs.DescriptiveComplexity.SatOcc

/-!
# A count-preserving 3-coloring gadget graph of a CNF formula

The gadget graph of `DescriptiveComplexity.Problems.ThreeColorability.SatGadget`
decides satisfiability but does not count models: its OR gate leaves its
output free when exactly one input is true. This file builds the graph the
counting reduction draws, whose proper 3-colorings are the models of the
formula, each `6 · 8 ^ g` times, `g` the number of non-first occurrences
(`DescriptiveComplexity.SatToColCount.card_proper`).

The vertices are a palette `T`, `F`, `B`; a pair of complementary **Boolean
vertices** per variable of the formula and per **gate**, i.e., per non-first
occurrence of a clause, adjacent to each other and to `B`, so colored `T` and
`F` in some order; a spoiler per empty clause, adjacent to the palette; and
nine triangle vertices per gate. A triangle whose three vertices are attached
to three Boolean or palette vertices has exactly two colorings when these are
not all equal and none otherwise (`DescriptiveComplexity.SatToColCount.tri_card`),
and the gate `z = p ∨ ℓ`, `p` the value of the prefix of the clause before the
occurrence and `ℓ` its literal, is exactly
`NAE(z, ¬p, ¬ℓ) ∧ NAE(¬p, z, F) ∧ NAE(¬ℓ, z, F)`
(`DescriptiveComplexity.SatToColCount.gate_iff`): three triangles per gate,
each with two colorings. The value of the last prefix of each clause is
forced true by an edge to `F`.
-/

namespace Lax859101Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

namespace SatToColCount

/-- The palette. -/
inductive Pal : Type
  /-- True. -/
  | T
  /-- False. -/
  | F
  /-- Base. -/
  | B
  deriving DecidableEq

instance : Fintype Pal := ⟨{.T, .F, .B}, by intro x; cases x <;> simp⟩

/-! ### Two Boolean facts -/

/-- The color of a truth value: `0` for true, `1` for false. -/
def bc (b : Bool) : Fin 3 := if b then 0 else 1

/-- Three colors are not all equal. -/
def NAE3 (a b c : Fin 3) : Prop := ¬(a = b ∧ b = c)

instance (a b c : Fin 3) : Decidable (NAE3 a b c) := by unfold NAE3; infer_instance

/-- **The gate**: `z = p ∨ ℓ` iff the three not-all-equal conditions hold. -/
theorem gate_iff (z p l : Bool) :
    (NAE3 (bc z) (bc !p) (bc !l) ∧ NAE3 (bc !p) (bc z) 1 ∧ NAE3 (bc !l) (bc z) 1) ↔
      z = (p || l) := by
  revert z p l
  decide

/-- **A triangle attached to three vertices of colors other than `B`** has two
colorings when the three colors are not all equal, none otherwise. -/
theorem tri_card : ∀ a b c : Fin 3, a ≠ 2 → b ≠ 2 → c ≠ 2 →
    Fintype.card {t : Fin 3 → Fin 3 //
        (t 0 ≠ t 1 ∧ t 0 ≠ t 2 ∧ t 1 ≠ t 2) ∧ t 0 ≠ a ∧ t 1 ≠ b ∧ t 2 ≠ c} =
      if NAE3 a b c then 2 else 0 := by
  decide

/-! ### The graph -/

variable (A : Type) [Lax904597.Sat.sat.Structure A] [LinearOrder A]

/-- The variables of the formula. -/
abbrev Var : Type := {x : A // Lax366625.CountingSat.SatOccurs A x}

/-- The gates: the non-first occurrences. -/
abbrev Gate : Type := {o : A × A × Bool // Chained o.1 o.2.1 o.2.2}

/-- The carriers of a Boolean pair: a variable or a gate. -/
abbrev Bv : Type := Var A ⊕ Gate A

/-- The vertices outside the triangles. -/
abbrev Core : Type := Pal ⊕ (Bv A × Bool) ⊕ {c : A // EmptyCl c}

/-- **The vertices**: the core, and nine triangle vertices per gate. -/
abbrev V : Type := Core A ⊕ (Gate A × Fin 3 × Fin 3)

variable {A}

omit [LinearOrder A] in
theorem satOccurs_of_occIn {c x : A} {s : Bool} (h : Lax799700.Common.SatOcc.OccIn c x s) : Lax366625.CountingSat.SatOccurs A x := by
  cases s
  · exact ⟨c, h.1, Or.inr h.2⟩
  · exact ⟨c, h.1, Or.inl h.2⟩

open Classical in
/-- **The prefix vertex** of an occurrence: the vertex whose color is the
disjunction of the literals of the clause up to it. The literal itself for
the first occurrence, the output of the gate otherwise. -/
noncomputable def prefixBv {c y : A} {t : Bool} (h : Lax799700.Common.SatOcc.OccIn c y t) : Bv A × Bool :=
  if hm : MinOcc c y t then (Sum.inl ⟨y, satOccurs_of_occIn h⟩, t)
  else (Sum.inr ⟨(c, y, t), h, hm⟩, true)

theorem prefixBv_of_min {c y : A} {t : Bool} (h : Lax799700.Common.SatOcc.OccIn c y t) (hm : MinOcc c y t) :
    prefixBv h = (Sum.inl ⟨y, satOccurs_of_occIn h⟩, t) := by
  rw [prefixBv, dif_pos hm]

theorem prefixBv_of_chained {c y : A} {t : Bool} (h : Chained c y t) :
    prefixBv h.1 = (Sum.inr ⟨(c, y, t), h⟩, true) := by
  rw [prefixBv, dif_neg h.2]

variable [Finite A]

/-- The predecessor of a gate. -/
noncomputable def pred (g : Gate A) : A × Bool :=
  ⟨Classical.choose (exists_succOcc g.2), Classical.choose (Classical.choose_spec
    (exists_succOcc g.2))⟩

theorem pred_spec (g : Gate A) : SuccOcc g.1.1 (pred g).1 (pred g).2 g.1.2.1 g.1.2.2 :=
  Classical.choose_spec (Classical.choose_spec (exists_succOcc g.2))

/-- The value of the predecessor's prefix, negated. -/
noncomputable def negPred (g : Gate A) : Core A :=
  Sum.inr (Sum.inl ((prefixBv (pred_spec g).1).1, !(prefixBv (pred_spec g).1).2))

/-- The gate output. -/
def zV (g : Gate A) : Core A := Sum.inr (Sum.inl (Sum.inr g, true))

/-- The negated literal of a gate. -/
def negLit (g : Gate A) : Core A :=
  Sum.inr (Sum.inl (Sum.inl ⟨g.1.2.1, satOccurs_of_occIn g.2.1⟩, !g.1.2.2))

/-- **The attachment of the triangles of a gate**: `NAE(z, ¬p, ¬ℓ)`,
`NAE(¬p, z, F)` and `NAE(¬ℓ, z, F)`. -/
noncomputable def outer (g : Gate A) : Fin 3 → Fin 3 → Core A :=
  ![![zV g, negPred g, negLit g], ![negPred g, zV g, Sum.inl .F],
    ![negLit g, zV g, Sum.inl .F] ]

/-- The edges between core vertices, in one direction. -/
def CoreE : Core A → Core A → Prop
  | Sum.inl p, Sum.inl q => p ≠ q
  | Sum.inr (Sum.inl (b, s)), Sum.inr (Sum.inl (b', s')) => b = b' ∧ s' = !s
  | Sum.inr (Sum.inl _), Sum.inl .B => True
  | Sum.inr (Sum.inl w), Sum.inl .F => ∃ (c x : A) (s : Bool) (h : MaxOcc c x s),
      w = prefixBv h.1
  | Sum.inr (Sum.inr _), Sum.inl _ => True
  | _, _ => False

/-- **The edges of the graph**, in one direction. -/
def E : V A → V A → Prop
  | Sum.inl u, Sum.inl v => CoreE u v
  | Sum.inr (g, j, r), Sum.inr (g', j', r') => g = g' ∧ j = j' ∧ r ≠ r'
  | Sum.inr (g, j, r), Sum.inl v => v = outer g j r
  | _, _ => False

/-- A proper 3-coloring. -/
def Proper (χ : V A → Fin 3) : Prop :=
  ∀ u v, E u v → χ u ≠ χ v

/-! ### Normalizing the palette -/

/-- A palette vertex. -/
abbrev palV (p : Pal) : Core A := Sum.inl p

/-- A Boolean vertex. -/
abbrev bvV (w : Bv A × Bool) : Core A := Sum.inr (Sum.inl w)

/-- A spoiler. -/
abbrev spV (c : {c : A // EmptyCl c}) : Core A := Sum.inr (Sum.inr c)

/-- The palette is colored `0`, `1`, `2`. -/
def Norm (χ : V A → Fin 3) : Prop :=
  χ (Sum.inl (palV .T)) = 0 ∧ χ (Sum.inl (palV .F)) = 1 ∧ χ (Sum.inl (palV .B)) = 2

theorem pal_injective {χ : V A → Fin 3} (hχ : Proper χ) :
    Function.Injective ![χ (Sum.inl (palV .T)), χ (Sum.inl (palV .F)), χ (Sum.inl (palV .B))] := by
  have h : ∀ p q : Pal, p ≠ q → χ (Sum.inl (palV p)) ≠ χ (Sum.inl (palV q)) :=
    fun p q hpq => hχ _ _ hpq
  have hTF := h .T .F (by decide)
  have hTB := h .T .B (by decide)
  have hFB := h .F .B (by decide)
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | rfl
    | exact absurd hij hTF | exact absurd hij hTB | exact absurd hij hFB
    | exact absurd hij.symm hTF | exact absurd hij.symm hTB | exact absurd hij.symm hFB

/-- The permutation of the colors the palette is colored with. -/
noncomputable def palPerm (χ : V A → Fin 3) (hχ : Proper χ) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (pal_injective hχ))

theorem proper_comp {χ : V A → Fin 3} (hχ : Proper χ) {f : Fin 3 → Fin 3}
    (hf : Function.Injective f) : Proper (f ∘ χ) :=
  fun u v huv h => hχ u v huv (hf h)

/-- **Normalizing the palette**: a proper coloring is a permutation of the
colors and a proper coloring with the palette colored `0`, `1`, `2`. -/
noncomputable def normEquiv :
    {χ : V A → Fin 3 // Proper χ} ≃
      Equiv.Perm (Fin 3) × {χ : V A → Fin 3 // Proper χ ∧ Norm χ} where
  toFun χ := (palPerm χ.1 χ.2, ⟨(palPerm χ.1 χ.2).symm ∘ χ.1,
    proper_comp χ.2 (palPerm χ.1 χ.2).symm.injective, by
      refine ⟨?_, ?_, ?_⟩ <;>
        simp only [Function.comp_apply, Equiv.symm_apply_eq] <;> rfl⟩)
  invFun p := ⟨p.1 ∘ p.2.1, proper_comp p.2.2.1 p.1.injective⟩
  left_inv χ := Subtype.ext (funext fun v => by simp)
  right_inv := by
    rintro ⟨σ, χ, hχ, hn⟩
    have h : palPerm (σ ∘ χ) (proper_comp hχ σ.injective) = σ := Equiv.ext fun i => by
      fin_cases i
      · change σ (χ _) = σ 0
        rw [hn.1]
      · change σ (χ _) = σ 1
        rw [hn.2.1]
      · change σ (χ _) = σ 2
        rw [hn.2.2]
    refine Prod.ext h (Subtype.ext (funext fun v => ?_))
    change (palPerm (σ ∘ χ) _).symm (σ (χ v)) = χ v
    rw [h, Equiv.symm_apply_apply]

/-! ### The triangles -/

/-- The core is properly colored. -/
def CoreProper (κ : Core A → Fin 3) : Prop :=
  ∀ u v, CoreE u v → κ u ≠ κ v

/-- The palette is colored `0`, `1`, `2`, on the core. -/
def NormC (κ : Core A → Fin 3) : Prop :=
  κ (palV .T) = 0 ∧ κ (palV .F) = 1 ∧ κ (palV .B) = 2

/-- A coloring of the triangle `j` of the gate `g`. -/
def TriOk (κ : Core A → Fin 3) (g : Gate A) (j : Fin 3) (t : Fin 3 → Fin 3) : Prop :=
  (t 0 ≠ t 1 ∧ t 0 ≠ t 2 ∧ t 1 ≠ t 2) ∧ t 0 ≠ κ (outer g j 0) ∧ t 1 ≠ κ (outer g j 1) ∧
    t 2 ≠ κ (outer g j 2)

theorem TriOk.ne {κ : Core A → Fin 3} {g : Gate A} {j : Fin 3} {t : Fin 3 → Fin 3}
    (h : TriOk κ g j t) {r r' : Fin 3} (hr : r ≠ r') : t r ≠ t r' := by
  obtain ⟨⟨h01, h02, h12⟩, -⟩ := h
  fin_cases r <;> fin_cases r' <;> simp_all [Ne.symm]

theorem TriOk.outer_ne {κ : Core A → Fin 3} {g : Gate A} {j : Fin 3} {t : Fin 3 → Fin 3}
    (h : TriOk κ g j t) (r : Fin 3) : t r ≠ κ (outer g j r) := by
  obtain ⟨-, h0, h1, h2⟩ := h
  fin_cases r
  · exact h0
  · exact h1
  · exact h2

/-- **The triangles split off**: a normalized proper coloring is a proper
coloring of the core and a coloring of each triangle. -/
noncomputable def triEquiv :
    {χ : V A → Fin 3 // Proper χ ∧ Norm χ} ≃
      Σ κ : {κ : Core A → Fin 3 // CoreProper κ ∧ NormC κ},
        ∀ q : Gate A × Fin 3, {t : Fin 3 → Fin 3 // TriOk κ.1 q.1 q.2 t} where
  toFun χ := ⟨⟨χ.1 ∘ Sum.inl, fun u v h => χ.2.1 (Sum.inl u) (Sum.inl v) h, χ.2.2⟩,
    fun q => ⟨fun r => χ.1 (Sum.inr (q.1, q.2, r)), by
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      · exact χ.2.1 (Sum.inr (q.1, q.2, 0)) (Sum.inr (q.1, q.2, 1)) ⟨rfl, rfl, by decide⟩
      · exact χ.2.1 (Sum.inr (q.1, q.2, 0)) (Sum.inr (q.1, q.2, 2)) ⟨rfl, rfl, by decide⟩
      · exact χ.2.1 (Sum.inr (q.1, q.2, 1)) (Sum.inr (q.1, q.2, 2)) ⟨rfl, rfl, by decide⟩
      · exact χ.2.1 (Sum.inr (q.1, q.2, 0)) (Sum.inl _) rfl
      · exact χ.2.1 (Sum.inr (q.1, q.2, 1)) (Sum.inl _) rfl
      · exact χ.2.1 (Sum.inr (q.1, q.2, 2)) (Sum.inl _) rfl⟩⟩
  invFun p := ⟨Sum.elim p.1.1 fun x => (p.2 (x.1, x.2.1)).1 x.2.2, by
    refine ⟨fun u v h => ?_, p.1.2.2⟩
    rcases u with u | ⟨g, j, r⟩ <;> rcases v with v | ⟨g', j', r'⟩
    · exact p.1.2.1 u v h
    · exact h.elim
    · obtain rfl := h
      exact (p.2 (g, j)).2.outer_ne r
    · obtain ⟨rfl, rfl, hr⟩ := h
      exact (p.2 (g, j)).2.ne hr⟩
  left_inv χ := Subtype.ext (funext fun v => by rcases v with v | ⟨g, j, r⟩ <;> rfl)
  right_inv _ := rfl

/-! ### The core colorings are the models -/

/-- Every triangle sees three colors not all equal. -/
def AllNAE (κ : Core A → Fin 3) : Prop :=
  ∀ (g : Gate A) (j : Fin 3), NAE3 (κ (outer g j 0)) (κ (outer g j 1)) (κ (outer g j 2))

theorem fin3_bc : ∀ a : Fin 3, a ≠ 2 → a = bc (decide (a = 0)) := by decide

theorem fin3_compl : ∀ a b : Fin 3, a ≠ 2 → b ≠ 2 → a ≠ b → (b = 0 ↔ a ≠ 0) := by decide

theorem fin3_ne_all : ∀ a : Fin 3, a ≠ 0 → a ≠ 1 → a ≠ 2 → False := by decide

/-- The assignment read off a core coloring. -/
def modelOf (κ : Core A → Fin 3) (x : A) : Prop :=
  ∃ h : Lax366625.CountingSat.SatOccurs A x, κ (bvV (Sum.inl ⟨x, h⟩, true)) = 0

omit [Finite A] in
theorem modelOf_iff (κ : Core A → Fin 3) (x : Var A) :
    modelOf κ x.1 ↔ κ (bvV (Sum.inl x, true)) = 0 :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

omit [Lax904597.Sat.sat.Structure A] in
/-- The order of the occurrences is well founded. -/
theorem occLt_wf : WellFounded fun p q : A × Bool => occLt p.1 p.2 q.1 q.2 := by
  have : IsTrans (A × Bool) fun p q => occLt p.1 p.2 q.1 q.2 :=
    ⟨fun _ _ _ h₁ h₂ => occLt_trans h₁ h₂⟩
  have : Std.Irrefl fun p q : A × Bool => occLt p.1 p.2 q.1 q.2 :=
    ⟨fun p => occLt_irrefl p.1 p.2⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

section Core

variable {κ : Core A → Fin 3} (hκ : CoreProper κ) (hn : NormC κ)

include hκ hn

omit [Finite A] in
theorem bv_ne_two (w : Bv A × Bool) : κ (bvV w) ≠ 2 := hn.2.2 ▸ hκ _ (palV .B) trivial

omit [Finite A] in
theorem bv_flip (b : Bv A) (s : Bool) : κ (bvV (b, !s)) = 0 ↔ κ (bvV (b, s)) ≠ 0 :=
  fin3_compl _ _ (bv_ne_two hκ hn _) (bv_ne_two hκ hn _) (hκ (bvV (b, s)) (bvV (b, !s)) ⟨rfl, rfl⟩)

omit [Finite A] in
/-- No clause is empty. -/
theorem not_emptyCl (c : {c : A // EmptyCl c}) : False :=
  fin3_ne_all (κ (spV c)) (hn.1 ▸ hκ _ (palV .T) trivial) (hn.2.1 ▸ hκ _ (palV .F) trivial)
    (hn.2.2 ▸ hκ _ (palV .B) trivial)

omit [Finite A] in
theorem lit_iff (x : Var A) (s : Bool) :
    κ (bvV (Sum.inl x, s)) = 0 ↔ Lax799700.Common.SatOcc.LitTrue (modelOf κ) x.1 s := by
  cases s
  · rw [Lax799700.Common.SatOcc.LitTrue, if_neg Bool.false_ne_true, modelOf_iff κ x]
    exact bv_flip hκ hn (Sum.inl x) true
  · rw [Lax799700.Common.SatOcc.LitTrue, if_pos rfl, modelOf_iff κ x]

/-- **The gate of a non-first occurrence computes the prefix
disjunction.** -/
theorem gate_value (hall : AllNAE κ) (g : Gate A) :
    κ (zV g) = 0 ↔ κ (bvV (prefixBv (pred_spec g).1)) = 0 ∨
      κ (bvV (Sum.inl ⟨g.1.2.1, satOccurs_of_occIn g.2.1⟩, g.1.2.2)) = 0 := by
  set z := decide (κ (zV g) = 0) with hz
  set p := decide (κ (bvV (prefixBv (pred_spec g).1)) = 0) with hp
  set l := decide (κ (bvV (Sum.inl ⟨g.1.2.1, satOccurs_of_occIn g.2.1⟩, g.1.2.2)) = 0) with hl
  have hzc : κ (zV g) = bc z := fin3_bc _ (bv_ne_two hκ hn _)
  have hpc : κ (negPred g) = bc !p := by
    change κ (bvV ((prefixBv (pred_spec g).1).1, !(prefixBv (pred_spec g).1).2)) = _
    rw [fin3_bc _ (bv_ne_two hκ hn _)]
    congr 1
    rw [hp]
    exact Bool.eq_iff_iff.mpr (by
      simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      exact bv_flip hκ hn _ _)
  have hlc : κ (negLit g) = bc !l := by
    change κ (bvV (Sum.inl ⟨g.1.2.1, satOccurs_of_occIn g.2.1⟩, !g.1.2.2)) = _
    rw [fin3_bc _ (bv_ne_two hκ hn _)]
    congr 1
    rw [hl]
    exact Bool.eq_iff_iff.mpr (by
      simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      exact bv_flip hκ hn _ _)
  have h0 := hall g 0
  have h1 := hall g 1
  have h2 := hall g 2
  simp only [outer, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  rw [hzc, hpc, hlc] at h0
  rw [hzc, hpc, hn.2.1] at h1
  rw [hzc, hlc, hn.2.1] at h2
  have hg := (gate_iff z p l).mp ⟨h0, h1, h2⟩
  rw [← decide_eq_true_iff (p := κ (zV g) = 0), ← hz, hg, Bool.or_eq_true, hp, hl,
    decide_eq_true_iff, decide_eq_true_iff]

/-- **The prefix vertex of every occurrence is colored by the prefix
disjunction.** -/
theorem prefix_value (hall : AllNAE κ) (c : A) :
    ∀ (p : A × Bool) (h : Lax799700.Common.SatOcc.OccIn c p.1 p.2),
      κ (bvV (prefixBv h)) = 0 ↔ PrefixOr (modelOf κ) c p.1 p.2 := by
  intro p
  induction p using (occLt_wf (A := A)).induction with
  | _ p ih =>
  obtain ⟨y, t⟩ := p
  intro h
  by_cases hm : MinOcc c y t
  · rw [prefixBv_of_min h hm, lit_iff hκ hn, prefixOr_iff h]
    exact ⟨Or.inr, fun h' => h'.resolve_left (not_prefixOrStrict_min hm)⟩
  · let g : Gate A := ⟨(c, y, t), h, hm⟩
    rw [prefixBv_of_chained (⟨h, hm⟩ : Chained c y t)]
    have hsucc := pred_spec g
    have ih' := ih (pred g) hsucc.2.2.1 hsucc.1
    change κ (zV g) = 0 ↔ _
    rw [gate_value hκ hn hall g, ih', lit_iff hκ hn, prefixOr_iff h,
      prefixOrStrict_succ hsucc]

end Core

theorem fin3_zero : ∀ a : Fin 3, a ≠ 1 → a ≠ 2 → a = 0 := by decide

theorem bc_eq_zero (b : Bool) : bc b = 0 ↔ b = true := by cases b <;> decide

theorem bc_ne_two (b : Bool) : bc b ≠ 2 := by cases b <;> decide

/-- **A core coloring gives a model.** -/
theorem satModel_modelOf {κ : Core A → Fin 3} (hκ : CoreProper κ) (hn : NormC κ)
    (hall : AllNAE κ) : Lax366625.CountingSat.SatModel A (modelOf κ) := by
  refine ⟨fun c hc => ?_, fun x hx => hx.1⟩
  by_cases hex : ∃ x s, Lax799700.Common.SatOcc.OccIn c x s
  · obtain ⟨x, s, hmax⟩ := exists_maxOcc hex
    have h1 : κ (bvV (prefixBv hmax.1)) ≠ 1 :=
      hn.2.1 ▸ hκ (bvV (prefixBv hmax.1)) (palV .F) ⟨c, x, s, hmax, rfl⟩
    have h0 := fin3_zero _ h1 (bv_ne_two hκ hn _)
    obtain ⟨y, t, hy, -, hT⟩ := (prefix_value hκ hn hall c (x, s) hmax.1).mp h0
    cases t
    · exact ⟨y, Or.inr ⟨hy.2, hT⟩⟩
    · exact ⟨y, Or.inl ⟨hy.2, hT⟩⟩
  · push Not at hex
    exact (not_emptyCl hκ hn ⟨c, hc, hex⟩).elim

/-! ### From a model to a core coloring -/

/-- The value of a carrier under an assignment: the variable, or the prefix
disjunction of the gate. -/
def baseVal (ν : A → Prop) : Bv A → Prop
  | Sum.inl x => ν x.1
  | Sum.inr g => PrefixOr ν g.1.1 g.1.2.1 g.1.2.2

/-- The value of a Boolean vertex. -/
def valBv (ν : A → Prop) (w : Bv A × Bool) : Prop :=
  if w.2 then baseVal ν w.1 else ¬baseVal ν w.1

omit [Finite A] in
theorem valBv_flip (ν : A → Prop) (b : Bv A) (s : Bool) :
    valBv ν (b, !s) ↔ ¬valBv ν (b, s) := by
  cases s <;> simp [valBv]

omit [Finite A] in
theorem valBv_prefix (ν : A → Prop) {c y : A} {t : Bool} (h : Lax799700.Common.SatOcc.OccIn c y t) :
    valBv ν (prefixBv h) ↔ PrefixOr ν c y t := by
  by_cases hm : MinOcc c y t
  · rw [prefixBv_of_min h hm, prefixOr_iff h]
    refine ⟨Or.inr, fun h' => ?_⟩
    exact h'.resolve_left (not_prefixOrStrict_min hm)
  · rw [prefixBv_of_chained (⟨h, hm⟩ : Chained c y t)]
    exact Iff.rfl

open Classical in
/-- **The core coloring of an assignment**: the palette `0`, `1`, `2`, every
Boolean vertex by its value. -/
noncomputable def colOf (ν : A → Prop) : Core A → Fin 3
  | Sum.inl .T => 0
  | Sum.inl .F => 1
  | Sum.inl .B => 2
  | Sum.inr (Sum.inl w) => bc (decide (valBv ν w))
  | Sum.inr (Sum.inr _) => 0

section OfModel

variable {ν : A → Prop} (hν : Lax366625.CountingSat.SatModel A ν)

include hν

omit [Finite A] in
theorem prefixOr_max {c x : A} {s : Bool} (hmax : MaxOcc c x s) : PrefixOr ν c x s := by
  obtain ⟨y, hy⟩ := hν.1 c hmax.1.1
  rcases hy with ⟨hp, hT⟩ | ⟨hn, hT⟩
  · exact prefixOr_of_max (t := true) hmax ⟨hmax.1.1, hp⟩ hT
  · exact prefixOr_of_max (t := false) hmax ⟨hmax.1.1, hn⟩ hT

omit [Finite A] in
theorem coreProper_colOf : CoreProper (colOf ν) := by
  classical
  intro u v h
  rcases u with p | (⟨b, s⟩ | c) <;> rcases v with q | (⟨b', s'⟩ | c')
  · cases p <;> cases q <;> first | exact absurd rfl h | (simp only [colOf]; decide)
  · exact h.elim
  · exact h.elim
  · cases q
    · exact h.elim
    · obtain ⟨c, x, t, hmax, hw⟩ := h
      change bc (decide (valBv ν (b, s))) ≠ 1
      rw [hw, decide_eq_true ((valBv_prefix ν hmax.1).mpr (prefixOr_max hν hmax))]
      decide
    · exact bc_ne_two _
  · obtain ⟨rfl, rfl⟩ := h
    change bc (decide (valBv ν (b, s))) ≠ bc (decide (valBv ν (b, !s)))
    by_cases hv : valBv ν (b, s)
    · rw [decide_eq_true hv, decide_eq_false ((not_not.mpr hv) ∘ (valBv_flip ν b s).mp)]
      decide
    · rw [decide_eq_false hv, decide_eq_true ((valBv_flip ν b s).mpr hv)]
      decide
  · exact h.elim
  · exfalso
    obtain ⟨x, hx⟩ := hν.1 c.1 c.2.1
    rcases hx with ⟨hp, -⟩ | ⟨hn, -⟩
    · exact c.2.2 x true ⟨c.2.1, hp⟩
    · exact c.2.2 x false ⟨c.2.1, hn⟩
  · exact h.elim
  · exact h.elim

omit hν in
omit [Finite A] in
theorem normC_colOf : NormC (colOf ν) := ⟨rfl, rfl, rfl⟩

omit hν in
theorem allNAE_colOf : AllNAE (colOf ν) := by
  classical
  intro g j
  have hsucc := pred_spec g
  have hz : colOf ν (zV g) = bc (decide (PrefixOr ν g.1.1 g.1.2.1 g.1.2.2)) := rfl
  have hp : colOf ν (negPred g) =
      bc !(decide (PrefixOr ν g.1.1 (pred g).1 (pred g).2)) := by
    change bc (decide (valBv ν ((prefixBv (pred_spec g).1).1, !(prefixBv (pred_spec g).1).2))) = _
    rw [valBv_flip, valBv_prefix ν (pred_spec g).1]
    by_cases h : PrefixOr ν g.1.1 (pred g).1 (pred g).2 <;> simp [h]
  have hl : colOf ν (negLit g) = bc !(decide (Lax799700.Common.SatOcc.LitTrue ν g.1.2.1 g.1.2.2)) := by
    change bc (decide (valBv ν (Sum.inl ⟨g.1.2.1, satOccurs_of_occIn g.2.1⟩, !g.1.2.2))) = _
    have hv : valBv ν (Sum.inl ⟨g.1.2.1, satOccurs_of_occIn g.2.1⟩, !g.1.2.2) ↔
        ¬Lax799700.Common.SatOcc.LitTrue ν g.1.2.1 g.1.2.2 := by
      rw [valBv_flip]
      exact Iff.rfl
    by_cases h : Lax799700.Common.SatOcc.LitTrue ν g.1.2.1 g.1.2.2
    · rw [decide_eq_false fun h' => hv.mp h' h, decide_eq_true h]
      rfl
    · rw [decide_eq_true (hv.mpr h), decide_eq_false h]
      rfl
  have hgate := (gate_iff (decide (PrefixOr ν g.1.1 g.1.2.1 g.1.2.2))
    (decide (PrefixOr ν g.1.1 (pred g).1 (pred g).2))
    (decide (Lax799700.Common.SatOcc.LitTrue ν g.1.2.1 g.1.2.2))).mpr (by
      rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff,
        decide_eq_true_iff, prefixOr_iff g.2.1, prefixOrStrict_succ hsucc])
  obtain ⟨h0, h1, h2⟩ := hgate
  fin_cases j
  · change NAE3 (colOf ν (zV g)) (colOf ν (negPred g)) (colOf ν (negLit g))
    rw [hz, hp, hl]
    exact h0
  · change NAE3 (colOf ν (negPred g)) (colOf ν (zV g)) 1
    rw [hz, hp]
    exact h1
  · change NAE3 (colOf ν (negLit g)) (colOf ν (zV g)) 1
    rw [hz, hl]
    exact h2

end OfModel

/-- **The core colorings are the models.** -/
noncomputable def modelEquiv :
    {κ : Core A → Fin 3 // (CoreProper κ ∧ NormC κ) ∧ AllNAE κ} ≃
      {ν : A → Prop // Lax366625.CountingSat.SatModel A ν} where
  toFun κ := ⟨modelOf κ.1, satModel_modelOf κ.2.1.1 κ.2.1.2 κ.2.2⟩
  invFun ν := ⟨colOf ν.1, ⟨coreProper_colOf ν.2, normC_colOf⟩, allNAE_colOf⟩
  left_inv := by
    classical
    rintro ⟨κ, ⟨hκ, hn⟩, hall⟩
    refine Subtype.ext (funext fun u => ?_)
    rcases u with p | (⟨b, s⟩ | c)
    · cases p
      · exact hn.1.symm
      · exact hn.2.1.symm
      · exact hn.2.2.symm
    · change bc (decide (valBv (modelOf κ) (b, s))) = κ (bvV (b, s))
      rw [fin3_bc (κ (bvV (b, s))) (bv_ne_two hκ hn _)]
      congr 1
      refine Bool.eq_iff_iff.mpr ?_
      rw [decide_eq_true_iff, decide_eq_true_iff]
      rcases b with x | g
      · exact (lit_iff hκ hn x s).symm
      · have hpre : κ (bvV (Sum.inr g, true)) = 0 ↔
            PrefixOr (modelOf κ) g.1.1 g.1.2.1 g.1.2.2 := by
          have := prefix_value hκ hn hall g.1.1 (g.1.2.1, g.1.2.2) g.2.1
          rw [prefixBv_of_chained g.2] at this
          exact this
        cases s
        · change ¬PrefixOr _ _ _ _ ↔ _
          have hf := bv_flip hκ hn (Sum.inr g) true
          simp only [Bool.not_true] at hf
          rw [hf]
          exact not_congr hpre.symm
        · exact hpre.symm
    · exact (not_emptyCl hκ hn c).elim
  right_inv := by
    classical
    rintro ⟨ν, hν⟩
    refine Subtype.ext (funext fun x => propext ⟨fun ⟨_, h⟩ => ?_, fun h => ⟨hν.2 x h, ?_⟩⟩)
    · change bc (decide (ν x)) = 0 at h
      exact of_decide_eq_true ((bc_eq_zero _).mp h)
    · change bc (decide (ν x)) = 0
      rw [decide_eq_true h]
      rfl

/-! ### The count -/

theorem outer_ne_two {κ : Core A → Fin 3} (hκ : CoreProper κ) (hn : NormC κ) (g : Gate A)
    (j r : Fin 3) : κ (outer g j r) ≠ 2 := by
  have hF : κ (palV .F) ≠ 2 := by rw [hn.2.1]; decide
  fin_cases j <;> fin_cases r
  all_goals first
    | exact bv_ne_two hκ hn _
    | exact hF

open Classical in
/-- **The number of proper 3-colorings of the gadget graph**: `6 · 8 ^ g`
times the number of models, `g` the number of non-first occurrences. -/
theorem card_proper :
    Nat.card {χ : V A → Fin 3 // Proper χ} =
      6 * 8 ^ Nat.card (Gate A) * Nat.card {ν : A → Prop // Lax366625.CountingSat.SatModel A ν} := by
  have := Fintype.ofFinite (Gate A)
  have := Fintype.ofFinite (Core A)
  rw [Nat.card_congr normEquiv, Nat.card_prod, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 3)),
    Fintype.card_perm, Fintype.card_fin, Nat.card_congr triEquiv, Nat.card_sigma,
    ← Nat.card_congr modelEquiv]
  have hterm : ∀ κ : {κ : Core A → Fin 3 // CoreProper κ ∧ NormC κ},
      Nat.card (∀ q : Gate A × Fin 3, {t : Fin 3 → Fin 3 // TriOk κ.1 q.1 q.2 t}) =
        if AllNAE κ.1 then 8 ^ Nat.card (Gate A) else 0 := by
    intro κ
    rw [Nat.card_pi]
    have hq : ∀ q : Gate A × Fin 3, Nat.card {t : Fin 3 → Fin 3 // TriOk κ.1 q.1 q.2 t} =
        if NAE3 (κ.1 (outer q.1 q.2 0)) (κ.1 (outer q.1 q.2 1)) (κ.1 (outer q.1 q.2 2))
        then 2 else 0 := fun q => by
      rw [← tri_card _ _ _ (outer_ne_two κ.2.1 κ.2.2 _ _ _)
        (outer_ne_two κ.2.1 κ.2.2 _ _ _) (outer_ne_two κ.2.1 κ.2.2 _ _ _)]
      exact Nat.card_eq_fintype_card.trans (Fintype.card_congr' rfl)
    by_cases hall : AllNAE κ.1
    · rw [if_pos hall,
        Finset.prod_congr rfl fun q _ => (hq q).trans (if_pos (hall q.1 q.2)),
        Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Nat.card_eq_fintype_card, pow_mul']
      rfl
    · rw [if_neg hall]
      obtain ⟨g, j, h⟩ : ∃ g j,
          ¬NAE3 (κ.1 (outer g j 0)) (κ.1 (outer g j 1)) (κ.1 (outer g j 2)) := by
        by_contra h'
        push Not at h'
        exact hall h'
      exact Finset.prod_eq_zero (Finset.mem_univ (g, j)) ((hq (g, j)).trans (if_neg h))
  rw [Finset.sum_congr rfl fun κ _ => hterm κ, ← Finset.sum_filter, Finset.sum_const,
    smul_eq_mul]
  have hcard : (Finset.univ.filter fun κ : {κ : Core A → Fin 3 // CoreProper κ ∧ NormC κ} =>
      AllNAE κ.1).card = Nat.card {κ : Core A → Fin 3 // (CoreProper κ ∧ NormC κ) ∧ AllNAE κ} := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
  rw [hcard, show Nat.factorial 3 = 6 from rfl]
  ring

end SatToColCount

end Lax859101Proofs.DescriptiveComplexity


