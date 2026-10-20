/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax175070Proofs.DescriptiveComplexity.Problems.Sat.CountingDecision
import Lax175070.CountDefinability
import Lax175070.SelectedSat
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
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

namespace Lax175070.SelectedSat
end Lax175070.SelectedSat

namespace Lax175070Proofs.DescriptiveComplexity.CountDefinable
end Lax175070Proofs.DescriptiveComplexity.CountDefinable

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.CountingSat
end Lax366625.CountingSat

namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Problems
end Lax904597.Problems

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax175070Proofs.DescriptiveComplexity
export Lax175070.SelectedSat (SelModel satSelStructure ssSel)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.Problems (DecisionProblem)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax366625.WitnessCounting (witnessCount)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax366625.CountingSat (SatModel)
end Lax175070Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax175070.SelectedSat (satSel selMark smSel)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax904597.Sat (sat)
end FirstOrder.Language

/-!
# SelMajSAT and SelEqSAT: complete problems for PP and C₌P

A CNF formula with a **selected variable** (`FirstOrder.Language.satSel`),
and the two counts of its models by the value of that variable
(`DescriptiveComplexity.SharpSelSAT true`, `DescriptiveComplexity.SharpSelSAT false`),
both in `#P`. The two decision problems comparing them:

* **SelMajSAT** (`DescriptiveComplexity.SelMajSAT`): the selected variable is
  true in more models than it is false – **`PP`-complete**
  (`DescriptiveComplexity.selMajSat_PP_complete`), the form the classical
  MajSAT of [Gill 1977][gill1977computational] takes when the instance may not
  count its own variables;
* **SelEqSAT** (`DescriptiveComplexity.SelEqSAT`): it is true in exactly as
  many models as it is false – **`C₌P`-complete**
  (`DescriptiveComplexity.selEqSat_CeqP_complete`).

Hardness is one construction for both: a problem of either class compares the
witness counts of two kernels; the pair kernel of
`DescriptiveComplexity.Counting.KernelPair` puts them in one kernel with a
selector, the parsimonious Tseitin interpretation turns it into a CNF formula
whose models are its witnesses, and the selected variable is the one of the
selector (`DescriptiveComplexity.PairSel.pairTseitinInterp`). The models in
which the selected variable is true are then the witnesses of the first
kernel, and the others those of the second.
-/

namespace FirstOrder

namespace Language

end Language

end FirstOrder

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The two counts -/

section Counts

variable (A : Type) [Lax175070.SelectedSat.satSel.Structure A]

/-- The vocabulary of the kernel: CNF formulas with a selected variable, and
the truth-assignment variable. -/
abbrev selSOLang : Language := Lax175070.SelectedSat.satSel.sum satAssignBlock.lang

/-- “Is selected”, in the kernel's vocabulary. -/
abbrev kSelSym : selSOLang.Relations 1 := Sum.inl Lax175070.SelectedSat.ssSel

/-- The truth-assignment symbol in the kernel's vocabulary. -/
abbrev kNuSelSym : selSOLang.Relations 1 := Sum.inr satNuSym

/-- The kernel of `#SAT`, read in the kernel's vocabulary. -/
def selHom : satSOLang →ᴸ selSOLang :=
  LHom.sumMap LHom.sumInl (LHom.id _)

/-- The kernel: a model of the formula, in which every selected variable has
the value `b`. -/
noncomputable def selKernel (b : Bool) : selSOLang.Sentence :=
  selHom.onSentence sharpSatKernel ⊓
    if b then FirstOrder.Language.Formula.iAlls (Fin 1)
                  ((FirstOrder.Language.Relations.formula₁ kSelSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
                    (FirstOrder.Language.Relations.formula₁ kNuSelSym (FirstOrder.Language.Term.var (Sum.inr 0)))) else FirstOrder.Language.Formula.iAlls (Fin 1)
                                                          ((FirstOrder.Language.Relations.formula₁ kSelSym (FirstOrder.Language.Term.var (Sum.inr 0))).imp
                                                            (FirstOrder.Language.BoundedFormula.not
                                                              (FirstOrder.Language.Relations.formula₁ kNuSelSym (FirstOrder.Language.Term.var (Sum.inr 0)))))

variable {A}

instance selHom_isExpansionOn (ρ : satAssignBlock.Assignment A) :
    @LHom.IsExpansionOn _ _ selHom A (@sumStructure _ _ A _ (satAssignBlock.structure ρ))
      (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) :=
  let := satAssignBlock.structure ρ
  ⟨fun f _ => by rcases f with f | f <;> rfl, fun r _ => by rcases r with r | r <;> rfl⟩

theorem realize_selKernel (b : Bool) (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize selSOLang A (@sumStructure _ _ A _ (satAssignBlock.structure ρ))
      (selKernel b)) ↔ Lax175070.SelectedSat.SelModel A b ((satAssignEquiv A).symm ρ) := by
  let := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := selSOLang) (M := A) kNuSelSym w ↔ (satAssignEquiv A).symm ρ (w 0) := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [selKernel, Lax175070.SelectedSat.SelModel]
  refine Formula.realize_inf.trans (and_congr ((LHom.realize_onSentence (φ := selHom) A
    sharpSatKernel).trans (realize_sharpSatKernel ρ)) ?_)
  cases b
  · rw [if_neg (by simp)]
    simp only [Bool.false_eq_true, iff_false, Formula.realize_iAlls, Formula.realize_imp,
      Formula.realize_not, Formula.realize_rel₁, Term.realize_var, Sum.elim_inr, hsub]
    exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩
  · rw [if_pos rfl]
    simp only [iff_true, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_rel₁,
      Term.realize_var, Sum.elim_inr, hsub]
    exact ⟨fun h a => h fun _ => a, fun h i => h (i 0)⟩

theorem card_selModel_eq_witnessCount (b : Bool) :
    Nat.card {ν : A → Prop // Lax175070.SelectedSat.SelModel A b ν} = Lax366625.WitnessCounting.witnessCount satAssignBlock (selKernel b) A :=
  Nat.card_congr (Equiv.subtypeEquiv (satAssignEquiv A) fun ν => by
    rw [realize_selKernel, Equiv.symm_apply_apply])

end Counts

/-- **The number of models of a CNF formula in which the selected variable
has the value `b`.** -/
noncomputable def SharpSelSAT (b : Bool) : Lax366625.CountingProblems.CountingProblem Lax175070.SelectedSat.satSel where
  Count := fun A inst => Nat.card {ν : A → Prop // @Lax175070.SelectedSat.SelModel A inst b ν}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_selModel_eq_witnessCount, card_selModel_eq_witnessCount]
    exact witnessCount_iso satAssignBlock (selKernel b) e

theorem sharpSelSat_apply (b : Bool) (A : Type) [Lax175070.SelectedSat.satSel.Structure A] :
    SharpSelSAT b A = Nat.card {ν : A → Prop // Lax175070.SelectedSat.SelModel A b ν} :=
  rfl

/-- Both counts are in `#P`. -/
theorem sharpSelSat_mem_sharpP (b : Bool) : SharpSelSAT b ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => (card_selModel_eq_witnessCount (A := A) b).symm)
    (sharpPDefinable_ofKernel satAssignBlock (selKernel b))

/-! ### The two problems -/

/-- **SelMajSAT**: the selected variable is true in more models than it is
false. -/
noncomputable def SelMajSAT : Lax904597.Problems.DecisionProblem Lax175070.SelectedSat.satSel where
  Holds := fun A inst => @SharpSelSAT false A inst < @SharpSelSAT true A inst
  iso_invariant := fun e => by
    rw [(SharpSelSAT false).iso_invariant e, (SharpSelSAT true).iso_invariant e]

/-- **SelEqSAT**: the selected variable is true in exactly as many models as
it is false. -/
noncomputable def SelEqSAT : Lax904597.Problems.DecisionProblem Lax175070.SelectedSat.satSel where
  Holds := fun A inst => @SharpSelSAT true A inst = @SharpSelSAT false A inst
  iso_invariant := fun e => by
    rw [(SharpSelSAT false).iso_invariant e, (SharpSelSAT true).iso_invariant e]

theorem selMajSat_mem_PP : SelMajSAT ∈ PP :=
  mem_countClass_of_sharpP (sharpSelSat_mem_sharpP true) (sharpSelSat_mem_sharpP false)
    fun _ _ _ _ => ⟨trivial, Iff.rfl⟩

theorem selEqSat_mem_CeqP : SelEqSAT ∈ CeqP :=
  mem_countClass_of_sharpP (sharpSelSat_mem_sharpP true) (sharpSelSat_mem_sharpP false)
    fun _ _ _ _ => ⟨trivial, Iff.rfl⟩

/-! ### Hardness: the Tseitin formula of a pair kernel, with the selector
selected -/

namespace PairSel

open Tseitin

variable {L : Language.{0, 0}} (B B' : Lax904597.SecondOrder.SOBlock) (φ : (L.sum B.lang).Sentence)
  (φ' : (L.sum B'.lang).Sentence)

/-- The selector of the pair block. -/
abbrev pairZ : (pairBlock B B').ι := Sum.inr (Sum.inr ())

/-- The block and the kernel of the pair, abbreviated. -/
abbrev PB : Lax904597.SecondOrder.SOBlock := pairBlock B B'

/-- The pair kernel, abbreviated. -/
noncomputable abbrev PK : (L.sum (PB B B').lang).Sentence := pairKernel B B' φ φ'

open Classical in
/-- **The Tseitin formula of the pair kernel, with the selector's variable
selected.** -/
noncomputable def pairTseitinInterp :
    Lax904597.Interpretations.FOInterpretation (L.sum Language.order) Lax175070.SelectedSat.satSel
      (SharpTseitinTag (PB B B') (PK B B' φ φ')) (tseitinDim (PB B B') (PK B B' φ φ')) where
  relFormula {n} R :=
    match R with
    | Sum.inl r => (sharpTseitinInterp (PB B B') (PK B B' φ φ')).relFormula r
    | Sum.inr s =>
      match n, s with
      | _, .sel => fun t =>
          match t 0 with
          | Sum.inl (Sum.inr (Sum.inl i)) =>
              if i = pairZ B B' then canonF ((PB B B').arity i) fun j => ((0 : Fin 1), j) else ⊥
          | _ => ⊥

section Correct

variable {B B' φ φ'} {A : Type} [L.Structure A] [LinearOrder A]

/-- The underlying CNF formula is the parsimonious Tseitin formula. -/
def satEquiv :
    (pairTseitinInterp B B' φ φ').Map A ≃[Lax904597.Sat.sat]
      (sharpTseitinInterp (PB B B') (PK B B' φ φ')).Map A :=
  ⟨Equiv.refl _, fun {_} f _ => isEmptyElim f, fun {_} _ _ => Iff.rfl⟩

variable (B B' φ φ') in
/-- The variable point of the selector, at a tuple. (The kernels are explicit:
left to unification, they would make it unfold the pair kernel.) -/
def selPt (x : Fin (tseitinDim (PB B B') (PK B B' φ φ')) → A) :
    (pairTseitinInterp B B' φ φ').Map A :=
  (Sum.inl (Sum.inr (Sum.inl (pairZ B B'))), x)

/-- The selected points are the canonical variable points of the selector. -/
theorem sel_iff (p : (pairTseitinInterp B B' φ φ').Map A) :
    RelMap (M := (pairTseitinInterp B B' φ φ').Map A) Lax175070.SelectedSat.ssSel ![p] ↔
      ∃ x, p = selPt B B' φ φ' x ∧ Canon 0 x := by
  classical
  obtain ⟨t, w⟩ := p
  rw [FOInterpretation.relMap_map]
  rcases t with (tc | vt) | i
  · refine iff_of_false id fun ⟨x, hx, _⟩ => ?_
    have h : Sum.inl (Sum.inl tc) = Sum.inl (Sum.inr (Sum.inl (pairZ B B'))) := (Prod.mk.inj hx).1
    exact Sum.inl_ne_inr (Sum.inl.inj h)
  · rcases vt with i | σ
    · change (if i = pairZ B B' then canonF ((PB B B').arity i) fun j => ((0 : Fin 1), j)
        else ⊥ : (L.sum Language.order).Formula (Fin 1 × Fin _)).Realize _ ↔ _
      by_cases hi : i = pairZ B B'
      · subst hi
        rw [if_pos rfl, realize_canonF]
        exact ⟨fun h => ⟨w, rfl, h⟩, fun ⟨x, hx, hc⟩ => by
          obtain rfl : w = x := (Prod.mk.inj hx).2
          exact hc⟩
      · rw [if_neg hi]
        refine iff_of_false id fun ⟨x, hx, _⟩ => hi ?_
        have h : Sum.inl (Sum.inr (Sum.inl i)) = Sum.inl (Sum.inr (Sum.inl (pairZ B B'))) :=
          (Prod.mk.inj hx).1
        exact Sum.inl.inj (Sum.inr.inj (Sum.inl.inj h))
    · refine iff_of_false id fun ⟨x, hx, _⟩ => ?_
      have h : Sum.inl (Sum.inr (Sum.inr σ)) = Sum.inl (Sum.inr (Sum.inl (pairZ B B'))) :=
        (Prod.mk.inj hx).1
      exact Sum.inr_ne_inl (Sum.inr.inj (Sum.inl.inj h))
  · refine iff_of_false id fun ⟨x, hx, _⟩ => ?_
    have h : Sum.inr i = Sum.inl (Sum.inr (Sum.inl (pairZ B B'))) := (Prod.mk.inj hx).1
    exact Sum.inr_ne_inl h

/-- The models of the marked formula are the models of the plain Tseitin
formula: the two universes meet only through this map. -/
def modelsEquiv :
    {ν : (pairTseitinInterp B B' φ φ').Map A → Prop //
        Lax366625.CountingSat.SatModel ((pairTseitinInterp B B' φ φ').Map A) ν} ≃
      {ν : (sharpTseitinInterp (PB B B') (PK B B' φ φ')).Map A → Prop //
        Lax366625.CountingSat.SatModel ((sharpTseitinInterp (PB B B') (PK B B' φ φ')).Map A) ν} where
  toFun ν := ⟨fun y => ν.1 (satEquiv.symm y), by
    have h := (satModel_equiv satEquiv.symm ν.1).mpr ν.2
    exact h⟩
  invFun ν := ⟨fun x => ν.1 (satEquiv x), (satModel_equiv satEquiv ν.1).mpr ν.2⟩
  left_inv ν := rfl
  right_inv ν := rfl

variable [Finite A] [Nonempty A]

/-- **The models with the selected variable at `b` are the witnesses of the
pair kernel whose selector is `b`.** -/
theorem sharpSelSat_eq (b : Bool) :
    SharpSelSAT b ((pairTseitinInterp B B' φ φ').Map A) =
      Nat.card {w : Witness (PB B B') (PK B B' φ φ') A // pairSel w.1 ↔ b = true} := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  rw [sharpSelSat_apply]
  -- the selected point, kept opaque: unfolding it makes the elaborator evaluate the dimension
  obtain ⟨pt, hpt⟩ : ∃ pt : (pairTseitinInterp B B' φ φ').Map A,
      pt = selPt B B' φ φ' (pad a₀ finZeroElim) := ⟨_, rfl⟩
  have hsel : RelMap (M := (pairTseitinInterp B B' φ φ').Map A) Lax175070.SelectedSat.ssSel ![pt] :=
    (sel_iff (B := B) (B' := B') (φ := φ) (φ' := φ') pt).mpr
      ⟨pad a₀ finZeroElim, hpt, canon_pad ha₀ 0 finZeroElim⟩
  have hpt' : ∀ p : (pairTseitinInterp B B' φ φ').Map A,
      RelMap (M := (pairTseitinInterp B B' φ φ').Map A) Lax175070.SelectedSat.ssSel ![p] → p = pt := by
    intro p hp
    obtain ⟨x, rfl, hx⟩ := (sel_iff (B := B) (B' := B') (φ := φ) (φ' := φ') p).mp hp
    rw [hpt, ← pad_pref_of_canon ha₀ (Nat.zero_le _) hx]
    exact congrArg (fun w => selPt B B' φ φ' (pad a₀ w)) (Subsingleton.elim _ _)
  have e1 : {ν : (pairTseitinInterp B B' φ φ').Map A → Prop //
        Lax175070.SelectedSat.SelModel ((pairTseitinInterp B B' φ φ').Map A) b ν} ≃
      {ν : (pairTseitinInterp B B' φ φ').Map A → Prop //
        Lax366625.CountingSat.SatModel ((pairTseitinInterp B B' φ φ').Map A) ν ∧ (ν pt ↔ b = true)} := by
    refine Equiv.subtypeEquivRight fun ν => ?_
    refine and_congr Iff.rfl ⟨fun h => h _ hsel, fun h p hp => ?_⟩
    rw [hpt' p hp]
    exact h
  have e2 := (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun ν : (pairTseitinInterp B B' φ φ').Map A → Prop =>
      Lax366625.CountingSat.SatModel ((pairTseitinInterp B B' φ φ').Map A) ν)
    fun ν => ν pt ↔ b = true).symm
  have e3 : {ν : {ν : (pairTseitinInterp B B' φ φ').Map A → Prop //
        Lax366625.CountingSat.SatModel ((pairTseitinInterp B B' φ φ').Map A) ν} // ν.1 pt ↔ b = true} ≃
      {ν : {ν : (sharpTseitinInterp (PB B B') (PK B B' φ φ')).Map A → Prop //
        Lax366625.CountingSat.SatModel ((sharpTseitinInterp (PB B B') (PK B B' φ φ')).Map A) ν} //
          ν.1 (satEquiv.symm.symm pt) ↔ b = true} :=
    Equiv.subtypeEquiv modelsEquiv fun ν => Iff.rfl
  have e4 : {ν : {ν : (sharpTseitinInterp (PB B B') (PK B B' φ φ')).Map A → Prop //
        Lax366625.CountingSat.SatModel ((sharpTseitinInterp (PB B B') (PK B B' φ φ')).Map A) ν} //
          ν.1 (satEquiv.symm.symm pt) ↔ b = true} ≃
      {μ : {μ : (PB B B').Assignment A // RealizeWith μ (PK B B' φ φ') finZeroElim} //
        μ.1 (pairZ B B') finZeroElim ↔ b = true} := by
    refine Equiv.subtypeEquiv (sharpModelEquiv (PB B B') (PK B B' φ φ') A ha₀) fun ν => ?_
    subst hpt
    exact Iff.rfl
  have e5 : {μ : {μ : (PB B B').Assignment A // RealizeWith μ (PK B B' φ φ') finZeroElim} //
        μ.1 (pairZ B B') finZeroElim ↔ b = true} ≃
      {w : Witness (PB B B') (PK B B' φ φ') A // pairSel w.1 ↔ b = true} :=
    Equiv.subtypeEquiv (Equiv.subtypeEquivRight fun μ =>
      (realize_iff_realizeWith (PB B B') (PK B B' φ φ') μ).symm) fun μ => Iff.rfl
  exact Nat.card_congr (e1.trans (e2.trans (e3.trans (e4.trans e5))))

theorem sharpSelSat_true :
    SharpSelSAT true ((pairTseitinInterp B B' φ φ').Map A) = Lax366625.WitnessCounting.witnessCount B φ A := by
  rw [sharpSelSat_eq, ← card_pairWitness_sel (φ := φ) (φ' := φ')]
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun w => by simp)

theorem sharpSelSat_false :
    SharpSelSAT false ((pairTseitinInterp B B' φ φ').Map A) = Lax366625.WitnessCounting.witnessCount B' φ' A := by
  rw [sharpSelSat_eq, ← card_pairWitness_not_sel (φ := φ) (φ' := φ')]
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun w => by simp)

end Correct

end PairSel

section Hardness

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **Every problem defined by a relation between two witness counts reduces
to the comparison of the two counts of a CNF formula by its selected
variable.** -/
noncomputable def CountDefinable.orderedReduction_sel (R : ℕ → ℕ → Prop)
    {P : Lax904597.Problems.DecisionProblem L} (B : Lax904597.SecondOrder.SOBlock) (φ : ((L.sum Language.order).sum B.lang).Sentence)
    (B' : Lax904597.SecondOrder.SOBlock) (φ' : ((L.sum Language.order).sum B'.lang).Sentence)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ R (Lax366625.WitnessCounting.witnessCount B φ A) (Lax366625.WitnessCounting.witnessCount B' φ' A)) :
    P ≤ᶠᵒ[≤] ⟨fun A inst => R (@SharpSelSAT true A inst) (@SharpSelSAT false A inst),
      fun e => by
        rw [(SharpSelSAT false).iso_invariant e, (SharpSelSAT true).iso_invariant e]⟩ where
  Tag := SharpTseitinTag (PairSel.PB B B') (PairSel.PK B B' φ φ')
  dim := tseitinDim (PairSel.PB B B') (PairSel.PK B B' φ φ')
  toInterpretation := (PairSel.pairTseitinInterp B B' φ φ').liftSource (orderCollapse L)
  correct A _ _ _ _ := by
    rw [h A]
    change _ ↔ R (SharpSelSAT true _) (SharpSelSAT false _)
    rw [(SharpSelSAT true).iso_invariant
        ((PairSel.pairTseitinInterp B B' φ φ').liftSourceLEquiv (orderCollapse L) A),
      (SharpSelSAT false).iso_invariant
        ((PairSel.pairTseitinInterp B B' φ φ').liftSourceLEquiv (orderCollapse L) A),
      PairSel.sharpSelSat_true, PairSel.sharpSelSat_false]

end Hardness

end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070.CountDefinability.CountDefinable

export Lax175070Proofs.DescriptiveComplexity.CountDefinable (orderedReduction_sel)

end Lax175070.CountDefinability.CountDefinable

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Hardness

variable {L : Language.{0, 0}} [L.IsRelational]

theorem selMajSat_PP_hard : PP.Hard SelMajSAT := by
  refine (hard_countClass_iff SelMajSAT).mpr ?_
  rintro L'' _ Q ⟨B, φ, B', φ', hφ⟩
  exact ⟨(CountDefinable.orderedReduction_sel (fun c d => d < c) B φ B' φ'
    fun A _ _ _ _ => (hφ A).2).toRel⟩

theorem selEqSat_CeqP_hard : CeqP.Hard SelEqSAT := by
  refine (hard_countClass_iff SelEqSAT).mpr ?_
  rintro L'' _ Q ⟨B, φ, B', φ', hφ⟩
  exact ⟨(CountDefinable.orderedReduction_sel (fun c d => c = d) B φ B' φ'
    fun A _ _ _ _ => (hφ A).2).toRel⟩

/-- **SelMajSAT is `PP`-complete.** -/
theorem selMajSat_PP_complete : PP.Complete SelMajSAT :=
  ⟨selMajSat_mem_PP, selMajSat_PP_hard⟩

/-- **SelEqSAT is `C₌P`-complete.** -/
theorem selEqSat_CeqP_complete : CeqP.Complete SelEqSAT :=
  ⟨selEqSat_mem_CeqP, selEqSat_CeqP_hard⟩

end Hardness

end Lax175070Proofs.DescriptiveComplexity


