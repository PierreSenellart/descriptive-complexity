/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax280166Proofs.DescriptiveComplexity.Problems.Hamilton.CircuitPerm
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

namespace Lax280166.CountingHamiltonCircuits
end Lax280166.CountingHamiltonCircuits

namespace Lax280166Proofs.DescriptiveComplexity.IsUCircuit
end Lax280166Proofs.DescriptiveComplexity.IsUCircuit

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax799700.Hamilton
end Lax799700.Hamilton

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax280166Proofs.DescriptiveComplexity
export Lax280166.CountingHamiltonCircuits (CycSucc IsCircuit IsUCircuit UCircuit)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax904597.Machines (IsLinOrd)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax799700.Hamilton (DGEdge SuccOf TourOn)
end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax280166Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax799700.Hamilton (dgArc digraph)
end FirstOrder.Language

/-!
# #Hamilton Circuit: counting the circuits of an undirected graph

The counting version of `DescriptiveComplexity.HamCircuit`: the number of Hamilton
circuits of a graph, a circuit being its **set of edges**
(`DescriptiveComplexity.IsUCircuit`) – the symmetric relation “`x` and `y` are
consecutive” – and not one of its two orientations.

## Membership

The certificate is still a linear order, and a circuit has `2n` of them: `n`
places to cut it and two directions to read it. The counting kernel
(`DescriptiveComplexity.sharpHamKernel`) fixes both: the order starts at the least
element of the instance, as for the directed problem, and of the two
neighbours of that element on the circuit it goes first to the smaller one
(`DescriptiveComplexity.Oriented`). Every circuit has exactly one such order: one
exists because reversing an order reverses its cyclic successor
(`DescriptiveComplexity.cycSucc_reverse`), and two of them with the same edges agree
at the root by the orientation rule, hence everywhere, by induction along the
circuit (`DescriptiveComplexity.cycSucc_of_sym`). Hence
`DescriptiveComplexity.sharpHamCircuit_mem_sharpP`.

Parsimonious hardness is in
`DescriptiveComplexity.Problems.Hamilton.CountingUndirectedHardness`.
-/

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section UCircuit

variable {A : Type}

/-- A relation has a tour iff it has an undirected circuit. -/
theorem tourOn_iff_exists_ucircuit {R : A → A → Prop} :
    Lax799700.Hamilton.TourOn R ↔ ∃ E, Lax280166.CountingHamiltonCircuits.IsUCircuit R E := by
  rw [tourOn_iff_exists_circuit]
  exact ⟨fun ⟨Nxt, h⟩ => ⟨_, Nxt, h, fun _ _ => Iff.rfl⟩, fun ⟨_, Nxt, h, _⟩ => ⟨Nxt, h⟩⟩

variable {B : Type}

/-- Undirected circuits transport along an equivalence commuting with the
relations. -/
theorem IsUCircuit.of_equiv (u : A ≃ B) {RA : A → A → Prop} {RB : B → B → Prop}
    (hR : ∀ a a', RA a a' ↔ RB (u a) (u a')) {E : A → A → Prop} (h : Lax280166.CountingHamiltonCircuits.IsUCircuit RA E) :
    Lax280166.CountingHamiltonCircuits.IsUCircuit RB fun b b' => E (u.symm b) (u.symm b') := by
  obtain ⟨Nxt, hN, hE⟩ := h
  exact ⟨_, hN.of_equiv u hR, fun b b' => hE _ _⟩

end UCircuit

end Lax280166Proofs.DescriptiveComplexity

namespace Lax280166.CountingHamiltonCircuits.IsUCircuit

export Lax280166Proofs.DescriptiveComplexity.IsUCircuit (of_equiv)

end Lax280166.CountingHamiltonCircuits.IsUCircuit

namespace Lax280166Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section UCircuit

variable {A : Type}

variable {B : Type}

/-- The undirected circuits of two relations an equivalence exchanges are in
bijection. -/
def ucircuitEquiv (u : A ≃ B) {RA : A → A → Prop} {RB : B → B → Prop}
    (hR : ∀ a a', RA a a' ↔ RB (u a) (u a')) :
    {E : A → A → Prop // Finite A ∧ Lax280166.CountingHamiltonCircuits.IsUCircuit RA E} ≃
      {E : B → B → Prop // Finite B ∧ Lax280166.CountingHamiltonCircuits.IsUCircuit RB E} where
  toFun N := ⟨fun b b' => N.1 (u.symm b) (u.symm b'), u.finite_iff.mp N.2.1,
    N.2.2.of_equiv u hR⟩
  invFun T := ⟨fun a a' => T.1 (u a) (u a'), u.finite_iff.mpr T.2.1, by
    have h := T.2.2.of_equiv u.symm (RB := RA) fun b b' => by
      rw [hR]
      simp
    simpa using h⟩
  left_inv N := Subtype.ext (funext fun a => funext fun a' => by simp)
  right_inv T := Subtype.ext (funext fun b => funext fun b' => by simp)

/-! ### One order per undirected circuit -/

/-- The orientation rule: from the least element, the circuit goes first to the
smaller of its two neighbours. -/
def Oriented [LE A] (C : A → A → Prop) : Prop :=
  ∀ x y z, IsBot x → C x y → C z x → y ≤ z

variable [LinearOrder A] [Finite A]

/-- **Two oriented cuts with the same edges have the same cyclic successor.** -/
theorem cycSucc_of_sym {Le Le' : A → A → Prop} (h : Lax904597.Machines.IsLinOrd Le) (h' : Lax904597.Machines.IsLinOrd Le') {a₀ : A}
    (ha₀ : IsBot a₀)
    (hsym : ∀ x y, (Lax280166.CountingHamiltonCircuits.CycSucc Le x y ∨ Lax280166.CountingHamiltonCircuits.CycSucc Le y x) ↔ (Lax280166.CountingHamiltonCircuits.CycSucc Le' x y ∨ Lax280166.CountingHamiltonCircuits.CycSucc Le' y x))
    (ho : Oriented (Lax280166.CountingHamiltonCircuits.CycSucc Le)) (ho' : Oriented (Lax280166.CountingHamiltonCircuits.CycSucc Le')) :
    ∀ x y, Lax280166.CountingHamiltonCircuits.CycSucc Le x y → Lax280166.CountingHamiltonCircuits.CycSucc Le' x y := by
  have hc : Lax280166.CountingHamiltonCircuits.IsCircuit (fun _ _ : A => True) (Lax280166.CountingHamiltonCircuits.CycSucc Le) :=
    ⟨Le, h, fun _ _ => Iff.rfl, fun _ _ _ => trivial⟩
  have hc' : Lax280166.CountingHamiltonCircuits.IsCircuit (fun _ _ : A => True) (Lax280166.CountingHamiltonCircuits.CycSucc Le') :=
    ⟨Le', h', fun _ _ => Iff.rfl, fun _ _ _ => trivial⟩
  obtain ⟨-, hfun, -, hinj, -, -⟩ := hc.local
  obtain ⟨htot', -, -, hinj', -, -⟩ := hc'.local
  refine hc.induction (P := fun x => ∀ y, Lax280166.CountingHamiltonCircuits.CycSucc Le x y → Lax280166.CountingHamiltonCircuits.CycSucc Le' x y) a₀ ?_ ?_
  · intro w hw
    rcases (hsym a₀ w).mp (Or.inl hw) with h₁ | h₁
    · exact h₁
    · obtain ⟨z', hz'⟩ := htot' a₀
      rcases (hsym a₀ z').mpr (Or.inl hz') with h₂ | h₂
      · rw [hfun _ _ _ hw h₂]
        exact hz'
      · rw [le_antisymm (ho a₀ w z' ha₀ hw h₂) (ho' a₀ z' w ha₀ hz' h₁)]
        exact hz'
  · intro x y hxy hP w hw
    have hxy' := hP y hxy
    rcases (hsym y w).mp (Or.inl hw) with h₁ | h₁
    · exact h₁
    · have hwx : w = x := hinj' _ _ _ h₁ hxy'
      subst hwx
      obtain ⟨w', hw'⟩ := htot' y
      rcases (hsym y w').mpr (Or.inl hw') with h₂ | h₂
      · rw [hfun _ _ _ hw h₂]
        exact hw'
      · rw [← hinj _ _ _ h₂ hxy]
        exact hw'

/-- **Undirected circuits are the oriented orders that start at the least
element**, bijectively. -/
theorem card_orientedTour_eq [Nonempty A] (R : A → A → Prop) (hRsym : ∀ x y, R x y → R y x) :
    Nat.card {Le : A → A → Prop // Lax904597.Machines.IsLinOrd Le ∧ (∀ x y, Lax799700.Hamilton.SuccOf Le x y → R x y) ∧
        (∀ x y, (∀ z, Le x z) → (∀ z, Le z y) → R y x) ∧
        (∀ x : A, IsBot x → ∀ y, Le x y) ∧ Oriented (Lax280166.CountingHamiltonCircuits.CycSucc Le)} =
      Nat.card {E : A → A → Prop // Lax280166.CountingHamiltonCircuits.IsUCircuit R E} := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  have hbot : ∀ x : A, IsBot x → x = a₀ := fun x hx => le_antisymm (hx a₀) (ha₀ x)
  refine Nat.card_congr (Equiv.ofBijective
    (fun Le => ⟨fun x y => Lax280166.CountingHamiltonCircuits.CycSucc Le.1 x y ∨ Lax280166.CountingHamiltonCircuits.CycSucc Le.1 y x, Lax280166.CountingHamiltonCircuits.CycSucc Le.1,
      ⟨Le.1, Le.2.1, fun _ _ => Iff.rfl,
        fun x y h => h.elim (Le.2.2.1 x y) fun ⟨hmax, hmin⟩ => Le.2.2.2.1 y x hmin hmax⟩,
      fun _ _ => Iff.rfl⟩)
    ⟨?_, ?_⟩)
  · intro L L' hval
    have hrel : ∀ x y, (Lax280166.CountingHamiltonCircuits.CycSucc L.1 x y ∨ Lax280166.CountingHamiltonCircuits.CycSucc L.1 y x) ↔
        (Lax280166.CountingHamiltonCircuits.CycSucc L'.1 x y ∨ Lax280166.CountingHamiltonCircuits.CycSucc L'.1 y x) := fun x y =>
      iff_of_eq (congrFun (congrFun (congrArg Subtype.val hval) x) y)
    exact Subtype.ext (linOrd_eq_of_cycSucc L.2.1 L'.2.1 (L.2.2.2.2.1 a₀ ha₀)
      (L'.2.2.2.2.1 a₀ ha₀) fun x y =>
        ⟨cycSucc_of_sym L.2.1 L'.2.1 ha₀ hrel L.2.2.2.2.2 L'.2.2.2.2.2 x y,
          cycSucc_of_sym L'.2.1 L.2.1 ha₀ (fun x y => (hrel x y).symm) L'.2.2.2.2.2
            L.2.2.2.2.2 x y⟩)
  · rintro ⟨E, Nxt, ⟨Le₀, h₀, hiff, hR⟩, hE⟩
    obtain ⟨Le₁, hlin₁, hmin₁, hcyc₁⟩ := exists_rooted_order h₀ a₀
    have hC₁ : ∀ x y, Lax280166.CountingHamiltonCircuits.CycSucc Le₁ x y ↔ Nxt x y := fun x y =>
      (hcyc₁ x y).trans (hiff x y).symm
    by_cases hor : Oriented (Lax280166.CountingHamiltonCircuits.CycSucc Le₁)
    · refine ⟨⟨Le₁, hlin₁, fun x y h => hR _ _ ((hC₁ _ _).mp (Or.inl h)),
        fun x y hx hy => hR _ _ ((hC₁ _ _).mp (Or.inr ⟨hy, hx⟩)),
        fun x hx y => hbot x hx ▸ hmin₁ y, hor⟩, Subtype.ext (funext fun x => funext fun y =>
          propext ((or_congr (hC₁ x y) (hC₁ y x)).trans (hE x y).symm))⟩
    · obtain ⟨Le₂, hlin₂, hmin₂, hcyc₂⟩ := exists_rooted_order hlin₁.reverse a₀
      have hC₂ : ∀ x y, Lax280166.CountingHamiltonCircuits.CycSucc Le₂ x y ↔ Nxt y x := fun x y =>
        (hcyc₂ x y).trans (cycSucc_reverse.trans (hC₁ y x))
      have hc₁ : Lax280166.CountingHamiltonCircuits.IsCircuit (fun _ _ : A => True) (Lax280166.CountingHamiltonCircuits.CycSucc Le₁) :=
        ⟨Le₁, hlin₁, fun _ _ => Iff.rfl, fun _ _ _ => trivial⟩
      obtain ⟨-, hfun, -, hinj, -, -⟩ := hc₁.local
      have hor₂ : Oriented (Lax280166.CountingHamiltonCircuits.CycSucc Le₂) := by
        unfold Oriented at hor
        push Not at hor
        obtain ⟨x, y, z, hx, hxy, hzx, hnot⟩ := hor
        intro x' y' z' hx' h₁ h₂
        rw [hbot x' hx'] at h₁ h₂
        rw [hbot x hx] at hxy hzx
        have e₁ : y' = z := hinj _ _ _ ((hC₁ _ _).mpr ((hC₂ _ _).mp h₁)) hzx
        have e₂ : z' = y := hfun _ _ _ ((hC₁ _ _).mpr ((hC₂ _ _).mp h₂)) hxy
        rw [e₁, e₂]
        exact le_of_lt hnot
      refine ⟨⟨Le₂, hlin₂, fun x y h => hRsym _ _ (hR _ _ ((hC₂ _ _).mp (Or.inl h))),
        fun x y hx hy => hRsym _ _ (hR _ _ ((hC₂ _ _).mp (Or.inr ⟨hy, hx⟩))),
        fun x hx y => hbot x hx ▸ hmin₂ y, hor₂⟩, Subtype.ext (funext fun x => funext fun y =>
          propext (((or_congr (hC₂ x y) (hC₂ y x)).trans or_comm).trans (hE x y).symm))⟩

end UCircuit

/-! ### The counting problem -/

section Problem

variable (A : Type) [Lax799700.Hamilton.digraph.Structure A]

end Problem

/-- **#Hamilton Circuit**: the number of Hamilton circuits of a graph, a
circuit being its set of edges. -/
noncomputable def SharpHamCircuit : Lax366625.CountingProblems.CountingProblem Lax799700.Hamilton.digraph where
  Count := fun A inst => Nat.card {E : A → A → Prop // @Lax280166.CountingHamiltonCircuits.UCircuit A inst E}
  iso_invariant := fun e => Nat.card_congr
    (ucircuitEquiv e.toEquiv fun a a' =>
      or_congr (relMap_equiv₂ e Lax799700.Hamilton.dgArc a a') (relMap_equiv₂ e Lax799700.Hamilton.dgArc a' a))

theorem sharpHamCircuit_apply (A : Type) [Lax799700.Hamilton.digraph.Structure A] :
    SharpHamCircuit A = Nat.card {E : A → A → Prop // Lax280166.CountingHamiltonCircuits.UCircuit A E} :=
  rfl

/-- **The support of #Hamilton Circuit is Hamilton Circuit.** -/
theorem sharpHamCircuit_support_iff (A : Type) [Lax799700.Hamilton.digraph.Structure A] [Finite A] :
    SharpHamCircuit.support A ↔ HamCircuit A := by
  rw [CountingProblem.support_iff, sharpHamCircuit_apply, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨E, hfin, hE⟩, -⟩
    exact ⟨hfin, tourOn_iff_exists_ucircuit.mpr ⟨E, hE⟩⟩
  · rintro ⟨hfin, h⟩
    obtain ⟨E, hE⟩ := tourOn_iff_exists_ucircuit.mp h
    exact ⟨⟨⟨E, hfin, hE⟩⟩, inferInstance⟩

/-! ### Membership -/

/-- The cyclic successor of the guessed order, as a formula. -/
noncomputable def cycF {α : Type} (x y : α) : dhcLang.Formula α :=
  FirstOrder.Language.Relations.formula₂ dhcVarSym (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y) ⊓
          FirstOrder.Language.BoundedFormula.not
            (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)) ⊓
        FirstOrder.Language.Formula.iAlls (Fin 1)
          ((FirstOrder.Language.Relations.formula₂ dhcVarSym (FirstOrder.Language.Term.var (Sum.inl x))
                  (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
                FirstOrder.Language.Relations.formula₂ dhcVarSym (FirstOrder.Language.Term.var (Sum.inr 0))
                  (FirstOrder.Language.Term.var (Sum.inl y))).imp
            (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inl x)) ⊔
              FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inl y)))) ⊔
      FirstOrder.Language.Formula.iAlls (Fin 1)
          (FirstOrder.Language.Relations.formula₂ dhcVarSym (FirstOrder.Language.Term.var (Sum.inr 0))
            (FirstOrder.Language.Term.var (Sum.inl x))) ⊓
        FirstOrder.Language.Formula.iAlls (Fin 1)
          (FirstOrder.Language.Relations.formula₂ dhcVarSym (FirstOrder.Language.Term.var (Sum.inl y))
            (FirstOrder.Language.Term.var (Sum.inr 0)))

/-- Kernel conjunct: the guessed order is oriented. -/
noncomputable def hamOrientClause : dhcLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      ((FirstOrder.Language.Formula.iAlls (Fin 1)
                (FirstOrder.Language.Relations.formula₂ dhcOrdSym (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
                  (FirstOrder.Language.Term.var (Sum.inr 0))) ⊓
              cycF (Sum.inr 0) (Sum.inr 1) ⊓
            cycF (Sum.inr 2) (Sum.inr 0)).imp
        (FirstOrder.Language.Relations.formula₂ dhcOrdSym (FirstOrder.Language.Term.var (Sum.inr 1))
          (FirstOrder.Language.Term.var (Sum.inr 2))))

/-- The first-order kernel of #Hamilton Circuit: the guessed relation is a
linear order carrying a tour of the edges, it starts at the least element of
the instance, and it is oriented. -/
noncomputable def sharpHamKernel : dhcLang.Sentence :=
  rootedHamKernel false ⊓ hamOrientClause

section Kernel

variable {A : Type} [Lax799700.Hamilton.digraph.Structure A] [LinearOrder A]

theorem realize_cycF (ρ : hamGuessBlock.Assignment A) {α : Type} (v : α → A) (x y : α) :
    (@Formula.Realize dhcLang A (@sumStructure _ _ A _ (hamGuessBlock.structure ρ)) _
        (cycF x y) v) ↔ Lax280166.CountingHamiltonCircuits.CycSucc (fun a b : A => ρ .le ![a, b]) (v x) (v y) := by
  let := hamGuessBlock.structure ρ
  have hVar : ∀ w : Fin 2 → A, RelMap (L := dhcLang) (M := A) dhcVarSym w ↔ ρ .le w :=
    fun _ => Iff.rfl
  simp only [cycF, Lax280166.CountingHamiltonCircuits.CycSucc, Lax799700.Hamilton.SuccOf, Formula.realize_sup, Formula.realize_inf,
    Formula.realize_not, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_equal,
    Formula.realize_rel₂, Term.realize_var, Sum.elim_inl, Sum.elim_inr, hVar]
  exact or_congr
    ⟨fun h => ⟨h.1.1, h.1.2, fun z h₁ h₂ => h.2 (fun _ => z) ⟨h₁, h₂⟩⟩,
      fun h => ⟨⟨h.1, h.2.1⟩, fun i hi => h.2.2 (i 0) hi.1 hi.2⟩⟩
    (and_congr ⟨fun h z => h fun _ => z, fun h i => h (i 0)⟩
      ⟨fun h z => h fun _ => z, fun h i => h (i 0)⟩)

/-- Realization of the kernel of #Hamilton Circuit. -/
theorem realize_sharpHamKernel (ρ : hamGuessBlock.Assignment A) :
    (@Sentence.Realize dhcLang A
        (@sumStructure _ _ A _ (hamGuessBlock.structure ρ)) sharpHamKernel) ↔
      Lax904597.Machines.IsLinOrd (fun x y : A => ρ .le ![x, y]) ∧
        (∀ x y : A, Lax799700.Hamilton.SuccOf (fun x y : A => ρ .le ![x, y]) x y → Lax799700.Hamilton.DGEdge x y) ∧
        (∀ x y : A, (∀ z, ρ .le ![x, z]) → (∀ z, ρ .le ![z, y]) → Lax799700.Hamilton.DGEdge y x) ∧
        (∀ x : A, IsBot x → ∀ y, ρ .le ![x, y]) ∧
        Oriented (Lax280166.CountingHamiltonCircuits.CycSucc fun x y : A => ρ .le ![x, y]) := by
  have hroot := realize_rootedHamKernel false ρ
  simp only [Bool.false_eq_true, ↓reduceIte] at hroot
  let := hamGuessBlock.structure ρ
  have hOrd : ∀ w : Fin 2 → A, RelMap (L := dhcLang) (M := A) dhcOrdSym w ↔ w 0 ≤ w 1 :=
    fun _ => Iff.rfl
  have horient : (@Sentence.Realize dhcLang A _ hamOrientClause) ↔
      Oriented (Lax280166.CountingHamiltonCircuits.CycSucc fun x y : A => ρ .le ![x, y]) := by
    simp only [hamOrientClause, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
      Formula.realize_inf, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
      hOrd, realize_cycF ρ, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨fun h x y z hx h₁ h₂ => h ![x, y, z] ⟨⟨fun w => hx (w 0), h₁⟩, h₂⟩,
      fun h i hi => h (i 0) (i 1) (i 2) (fun z => hi.1.1 fun _ => z) hi.1.2 hi.2⟩
  rw [sharpHamKernel, Sentence.Realize, Formula.realize_inf]
  rw [← and_assoc, ← and_assoc, ← and_assoc]
  refine and_congr (hroot.trans ?_) horient
  rw [and_assoc, and_assoc]

end Kernel

/-- **#Hamilton Circuit is in `#P`**: a circuit has exactly one oriented cut at
the least element of the instance. -/
theorem sharpHamCircuit_mem_sharpP : SharpHamCircuit ∈ SharpP := by
  refine ⟨hamGuessBlock, sharpHamKernel, fun A _ _ hfin _ => ?_⟩
  rw [sharpHamCircuit_apply]
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_iff_right hfin)).trans
    ((card_orientedTour_eq (fun x y : A => Lax799700.Hamilton.DGEdge x y) fun x y h => h.symm).symm.trans
      (Nat.card_congr (Equiv.subtypeEquiv (hamAssignEquiv A)
        fun ρ => (realize_sharpHamKernel ρ))).symm)

end Lax280166Proofs.DescriptiveComplexity


