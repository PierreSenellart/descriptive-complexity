/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax175070Proofs.DescriptiveComplexity.Problems.Sat.Counting
import Lax175070Proofs.DescriptiveComplexity.Problems.Sat.Hardness
import Lax175070Proofs.DescriptiveComplexity.Problems.Sat.TseitinUnique
import Lax175070Proofs.DescriptiveComplexity.Counting.Subtractive
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

namespace Lax366625.CountingProblems
end Lax366625.CountingProblems

namespace Lax366625.CountingSat
end Lax366625.CountingSat

namespace Lax366625.WitnessCounting
end Lax366625.WitnessCounting

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

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
export Lax366625.WitnessCounting (SharpPDefinable witnessCount)
end Lax175070Proofs.DescriptiveComplexity

namespace Lax175070Proofs.DescriptiveComplexity
export Lax366625.CountingSat (SatModel SatOccurs)
end Lax175070Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax904597.Sat (sat satIsClause satNegIn satPosIn)
end FirstOrder.Language

/-!
# #SAT is parsimoniously `#P`-complete

The counting form of the Cook–Levin theorem: every `#P`-definable counting
problem reduces to `DescriptiveComplexity.SharpSAT` by an ordered *parsimonious*
reduction (`DescriptiveComplexity.sharpSat_parsimoniousHard_of_sharpPDefinable`), so #SAT is
parsimoniously `#P`-complete (`DescriptiveComplexity.sharpSat_sharpP_parsimoniousComplete`).

The reduction is the Tseitin interpretation of
`DescriptiveComplexity.Problems.Sat.Hardness`, and the reason it preserves the number
of solutions is the classical one: the gate variables of a Tseitin encoding are
functionally determined by the input variables
(`DescriptiveComplexity.Tseitin.gates_unique`), and every variable of the encoding sits
at a canonically padded tuple (`DescriptiveComplexity.Tseitin.litSem_varCanon`), so a
model of the encoding is exactly an assignment of the block satisfying the
kernel.

One thing has to be added to the decision reduction. A block variable at a
tuple that the kernel never mentions occurs in no clause of the encoding, so it
is not a variable of the CNF formula, while the witness count ranges over all
assignments of the block. The interpretation `DescriptiveComplexity.sharpTseitinInterp`
therefore adds one tautological clause `R(ā) ∨ ¬R(ā)` per block variable and
tuple, which makes each of them occur without constraining anything.
-/

namespace Lax175070Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Tseitin

section Interp

variable {L : Language.{0, 0}} (B : Lax904597.SecondOrder.SOBlock) (φ : (L.sum B.lang).Sentence)

/-- The tags of the parsimonious Tseitin interpretation: those of the Tseitin
interpretation, and one tautological clause per block variable. -/
abbrev SharpTseitinTag : Type :=
  TseitinTag B φ ⊕ B.ι

open Classical in
/-- The defining formula of `satPosIn` (`s = true`) and `satNegIn`
(`s = false`): the literals of the Tseitin interpretation, and the block
variable `i` at the tuple of its tautological clause, with both signs. -/
noncomputable def sharpLitFml (s : Bool) (tc tx : SharpTseitinTag B φ) :
    (L.sum Language.order).Formula (Fin 2 × Fin (tseitinDim B φ)) :=
  match tc, tx with
  | Sum.inl tc, Sum.inl tx => tseitinLitFml B φ s tc tx
  | Sum.inr i, Sum.inl (Sum.inr (Sum.inl i')) =>
      if i = i' then
        canonF (B.arity i) (fun j => ((0 : Fin 2), j)) ⊓
          eqTupF (fun j => ((0 : Fin 2), j)) fun j => ((1 : Fin 2), j)
      else ⊥
  | _, _ => ⊥

/-- The parsimonious Tseitin interpretation: the CNF instance of the Tseitin
encoding of `φ`, with one tautological clause per block variable and
canonically padded tuple. -/
noncomputable def sharpTseitinInterp :
    Lax904597.Interpretations.FOInterpretation (L.sum Language.order) Lax904597.Sat.sat (SharpTseitinTag B φ)
      (tseitinDim B φ) where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun t =>
        (match t 0 with
         | Sum.inl tc => (tseitinInterp B φ).relFormula Lax904597.Sat.satIsClause fun _ => tc
         | Sum.inr i => canonF (B.arity i) fun j => ((0 : Fin 1), j))
    | _, .posIn => fun t => sharpLitFml B φ true (t 0) (t 1)
    | _, .negIn => fun t => sharpLitFml B φ false (t 0) (t 1)

/-! ### The points of the interpreted instance -/

section Points

variable {B φ} {A : Type}

/-- A point of the Tseitin instance, as a point of the parsimonious one. -/
def sharpOldPt (e : (tseitinInterp B φ).Map A) : (sharpTseitinInterp B φ).Map A :=
  (Sum.inl e.1, e.2)

/-- The tautological clause of the block variable `i` at the tuple `u`. -/
def sharpTautPt (i : B.ι) (u : Fin (tseitinDim B φ) → A) : (sharpTseitinInterp B φ).Map A :=
  (Sum.inr i, u)

/-- The propositional variable indexed by `vt` at the tuple `x`, as a point of
the Tseitin instance. -/
def tseitinVarPt (vt : B.ι ⊕ Σ m, NodeAt φ m) (x : Fin (tseitinDim B φ) → A) :
    (tseitinInterp B φ).Map A :=
  (Sum.inr vt, x)

theorem sharpPt_cases (e : (sharpTseitinInterp B φ).Map A) :
    (∃ x, e = sharpOldPt x) ∨ ∃ i u, e = sharpTautPt i u := by
  obtain ⟨t, u⟩ := e
  rcases t with t | i
  · exact Or.inl ⟨(t, u), rfl⟩
  · exact Or.inr ⟨i, u, rfl⟩

theorem oldPt_injective {e e' : (tseitinInterp B φ).Map A} (h : sharpOldPt e = sharpOldPt e') :
    e = e' := by
  have h1 : (sharpOldPt e).1 = (sharpOldPt e').1 := congrArg Prod.fst h
  have h2 : (sharpOldPt e).2 = (sharpOldPt e').2 := congrArg Prod.snd h
  exact Prod.ext (Sum.inl.inj h1) h2

theorem oldPt_ne_tautPt (e : (tseitinInterp B φ).Map A) (i : B.ι)
    (u : Fin (tseitinDim B φ) → A) : sharpOldPt e ≠ sharpTautPt i u :=
  fun h => Sum.inl_ne_inr (congrArg Prod.fst h)

end Points

/-! ### Characterization of the interpreted relations -/

section Characterizations

variable {B φ} {A : Type} [L.Structure A] [LinearOrder A]

/-- On the points of the Tseitin instance, the clauses are those of the Tseitin
instance. -/
theorem sharp_isClause_old (e : (tseitinInterp B φ).Map A) :
    RelMap (M := (sharpTseitinInterp B φ).Map A) Lax904597.Sat.satIsClause ![sharpOldPt e] ↔
      RelMap (M := (tseitinInterp B φ).Map A) Lax904597.Sat.satIsClause ![e] := by
  refine iff_of_eq (congrArg (Formula.Realize _) (funext fun p => ?_))
  obtain ⟨i, j⟩ := p
  fin_cases i
  rfl

/-- On the points of the Tseitin instance, the literals are those of the
Tseitin instance. -/
theorem sharp_lit_old (R : Lax904597.Sat.sat.Relations 2) (c x : (tseitinInterp B φ).Map A) :
    RelMap (M := (sharpTseitinInterp B φ).Map A) R ![sharpOldPt c, sharpOldPt x] ↔
      RelMap (M := (tseitinInterp B φ).Map A) R ![c, x] := by
  cases R <;>
  · refine iff_of_eq (congrArg (Formula.Realize _) (funext fun p => ?_))
    obtain ⟨i, j⟩ := p
    fin_cases i <;> rfl

/-- A clause of the Tseitin instance has no literal at a tautological
clause. -/
theorem sharp_lit_old_taut (R : Lax904597.Sat.sat.Relations 2) (c : (tseitinInterp B φ).Map A)
    (i : B.ι) (u : Fin (tseitinDim B φ) → A) :
    ¬RelMap (M := (sharpTseitinInterp B φ).Map A) R ![sharpOldPt c, sharpTautPt i u] := by
  cases R <;> exact fun h => h

/-- The literals of a clause of the Tseitin instance are points of the Tseitin
instance, and are its literals there. -/
theorem sharp_lit_old_iff (R : Lax904597.Sat.sat.Relations 2) (c : (tseitinInterp B φ).Map A)
    (e : (sharpTseitinInterp B φ).Map A) :
    RelMap (M := (sharpTseitinInterp B φ).Map A) R ![sharpOldPt c, e] ↔
      ∃ x, e = sharpOldPt x ∧ RelMap (M := (tseitinInterp B φ).Map A) R ![c, x] := by
  rcases sharpPt_cases e with ⟨x, rfl⟩ | ⟨i, u, rfl⟩
  · refine (sharp_lit_old R c x).trans ⟨fun h => ⟨x, rfl, h⟩, ?_⟩
    rintro ⟨x', hx', h⟩
    exact (oldPt_injective hx') ▸ h
  · refine iff_of_false (sharp_lit_old_taut R c i u) ?_
    rintro ⟨x, hx, -⟩
    exact oldPt_ne_tautPt x i u hx.symm

/-- The tautological clauses sit at the canonically padded tuples. -/
theorem sharp_isClause_taut (i : B.ι) (u : Fin (tseitinDim B φ) → A) :
    RelMap (M := (sharpTseitinInterp B φ).Map A) Lax904597.Sat.satIsClause ![sharpTautPt i u] ↔
      Canon (B.arity i) u := by
  rw [FOInterpretation.relMap_map]
  exact realize_canonF

/-- The one variable of a tautological clause, with either sign: the block
variable of the clause at the tuple of the clause. -/
theorem sharp_lit_taut_iff (R : Lax904597.Sat.sat.Relations 2) (i : B.ι)
    (u : Fin (tseitinDim B φ) → A) (e : (sharpTseitinInterp B φ).Map A) :
    RelMap (M := (sharpTseitinInterp B φ).Map A) R ![sharpTautPt i u, e] ↔
      Canon (B.arity i) u ∧ e = sharpOldPt (tseitinVarPt (Sum.inl i) u) := by
  classical
  obtain ⟨t, x⟩ := e
  have hne : ∀ {t' : SharpTseitinTag B φ}, t' ≠ Sum.inl (Sum.inr (Sum.inl i)) →
      ¬((t', x) : (sharpTseitinInterp B φ).Map A) = sharpOldPt (tseitinVarPt (Sum.inl i) u) :=
    fun ht h => ht (congrArg Prod.fst h)
  rcases t with ((tcl | (i' | σ)) | j)
  · refine iff_of_false ?_ fun h => hne (fun h' => Sum.inl_ne_inr (Sum.inl.inj h')) h.2
    cases R <;> exact fun h => h
  · have hf : RelMap (M := (sharpTseitinInterp B φ).Map A) R
          ![sharpTautPt i u, (Sum.inl (Sum.inr (Sum.inl i')), x)] ↔
        (if i = i' then
            canonF (L := L) (B.arity i) (fun j => ((0 : Fin 2), j)) ⊓
              eqTupF (fun j => ((0 : Fin 2), j)) fun j => ((1 : Fin 2), j)
          else ⊥).Realize
          (fun p : Fin 2 × Fin (tseitinDim B φ) => (![u, x] p.1) p.2) := by
      cases R <;>
      · refine iff_of_eq (congrArg (Formula.Realize _) (funext fun p => ?_))
        obtain ⟨k, j⟩ := p
        fin_cases k <;> rfl
    rw [hf]
    split_ifs with h
    · subst h
      rw [Formula.realize_inf, realize_canonF, realize_eqTupF]
      constructor
      · rintro ⟨hc, hx⟩
        have hxu : x = u := hx
        exact ⟨hc, hxu ▸ rfl⟩
      · rintro ⟨hc, hx⟩
        exact ⟨hc, congrArg Prod.snd hx⟩
    · refine iff_of_false (fun hbot => hbot) fun hx => h ?_
      exact (Sum.inl.inj (Sum.inr.inj (Sum.inl.inj (congrArg Prod.fst hx.2)))).symm
  · refine iff_of_false ?_ fun h =>
      hne (fun h' => Sum.inr_ne_inl (Sum.inr.inj (Sum.inl.inj h'))) h.2
    cases R <;> exact fun h => h
  · refine iff_of_false ?_ fun h => hne Sum.inr_ne_inl h.2
    cases R <;> exact fun h => h

end Characterizations

/-! ### Models of the interpreted instance are assignments of the block -/

section Models

variable {B φ} {A : Type} [L.Structure A] [LinearOrder A]

/-- **Variables of the interpreted instance**: an element occurring in a clause
is a propositional variable of the encoding at a tuple canonical for it. -/
theorem sharp_occurs_canon {e : (sharpTseitinInterp B φ).Map A}
    (he : Lax366625.CountingSat.SatOccurs ((sharpTseitinInterp B φ).Map A) e) :
    ∃ vt x, e = sharpOldPt (tseitinVarPt vt x) ∧ VarCanon vt x := by
  obtain ⟨c, hc, hlit⟩ := he
  rcases sharpPt_cases c with ⟨⟨tc, u⟩, rfl⟩ | ⟨i, u, rfl⟩
  · have hc' := (sharp_isClause_old _).mp hc
    obtain ⟨s, ⟨tx, x⟩, rfl, hx⟩ : ∃ (s : Bool) (y : (tseitinInterp B φ).Map A),
        e = sharpOldPt y ∧
          RelMap (M := (tseitinInterp B φ).Map A) (if s then Lax904597.Sat.satPosIn else Lax904597.Sat.satNegIn)
            ![(tc, u), y] := by
      rcases hlit with h | h
      · obtain ⟨y, hy, hy'⟩ := (sharp_lit_old_iff Lax904597.Sat.satPosIn _ e).mp h
        exact ⟨true, y, hy, hy'⟩
      · obtain ⟨y, hy, hy'⟩ := (sharp_lit_old_iff Lax904597.Sat.satNegIn _ e).mp h
        exact ⟨false, y, hy, hy'⟩
    have hls := (tseitin_lit_iff B φ s tc tx u x).mp hx
    rcases tc with tcl | vt
    swap
    · exact absurd hc' (tseitin_isClause_var B φ vt u)
    rcases tcl with ⟨σp, k⟩ | u'
    · rcases tx with txl | vt
      · exact hls.elim
      · exact ⟨vt, x, rfl, litSem_varCanon s φ (maxCtx_le_tseitinDim B φ) σp.2 k u vt x
          ((tseitin_isClause_node B φ σp k u).mp hc') hls⟩
    · rcases tx with txl | vt
      · exact hls.elim
      · rcases vt with i | σp'
        · exact hls.elim
        · obtain ⟨-, rfl, -, hcx⟩ := hls
          exact ⟨Sum.inr ⟨0, rootAt φ⟩, x, rfl, hcx⟩
  · have hcan := (sharp_isClause_taut _ _).mp hc
    have he : e = sharpOldPt (tseitinVarPt (Sum.inl i) u) := by
      rcases hlit with h | h
      · exact ((sharp_lit_taut_iff Lax904597.Sat.satPosIn i u e).mp h).2
      · exact ((sharp_lit_taut_iff Lax904597.Sat.satNegIn i u e).mp h).2
    exact ⟨Sum.inl i, u, he, hcan⟩

/-- Every block variable at a canonically padded tuple is a variable of the
interpreted instance: it occurs in its tautological clause. -/
theorem sharp_occurs_block (i : B.ι) {u : Fin (tseitinDim B φ) → A}
    (hu : Canon (B.arity i) u) :
    Lax366625.CountingSat.SatOccurs ((sharpTseitinInterp B φ).Map A) (sharpOldPt (tseitinVarPt (Sum.inl i) u)) :=
  ⟨sharpTautPt i u, (sharp_isClause_taut _ _).mpr hu,
    Or.inl ((sharp_lit_taut_iff Lax904597.Sat.satPosIn i u _).mpr ⟨hu, rfl⟩)⟩

/-- The truth assignment of the interpreted instance determined by an
assignment of the block, before its restriction to the variables of the
instance. -/
def sharpVal (μ : B.Assignment A) (e : (sharpTseitinInterp B φ).Map A) : Prop :=
  match e with
  | (Sum.inl (Sum.inr vt), x) => tseitinVal B φ μ vt x
  | _ => False

omit [LinearOrder A] in
theorem sharpVal_varPt (μ : B.Assignment A) (vt : B.ι ⊕ Σ m, NodeAt φ m)
    (x : Fin (tseitinDim B φ) → A) :
    sharpVal μ (sharpOldPt (tseitinVarPt vt x)) ↔ tseitinVal B φ μ vt x :=
  Iff.rfl

/-- The clauses of the Tseitin instance hold under a truth assignment of the
parsimonious instance satisfying all its clauses. -/
theorem sharp_old_clauses {ν : (sharpTseitinInterp B φ).Map A → Prop}
    (hν : ∀ c : (sharpTseitinInterp B φ).Map A, RelMap Lax904597.Sat.satIsClause ![c] →
      ∃ x, (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ ν x) ∨ (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ¬ν x))
    (c : (tseitinInterp B φ).Map A) (hc : RelMap Lax904597.Sat.satIsClause ![c]) :
    ∃ x, (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ ν (sharpOldPt x)) ∨
      (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ¬ν (sharpOldPt x)) := by
  obtain ⟨e, he⟩ := hν (sharpOldPt c) ((sharp_isClause_old _).mpr hc)
  rcases he with ⟨hp, hv⟩ | ⟨hn, hv⟩
  · obtain ⟨x, rfl, hx⟩ := (sharp_lit_old_iff Lax904597.Sat.satPosIn c e).mp hp
    exact ⟨x, Or.inl ⟨hx, hv⟩⟩
  · obtain ⟨x, rfl, hx⟩ := (sharp_lit_old_iff Lax904597.Sat.satNegIn c e).mp hn
    exact ⟨x, Or.inr ⟨hx, hv⟩⟩

/-- The truth assignment determined by an assignment of the block realizing the
kernel satisfies every clause of the parsimonious instance. -/
theorem sharpVal_clauses {a₀ : A} (ha₀ : IsBot a₀) (μ : B.Assignment A)
    (hμ : RealizeWith μ φ finZeroElim) (c : (sharpTseitinInterp B φ).Map A)
    (hc : RelMap Lax904597.Sat.satIsClause ![c]) :
    ∃ x, (RelMap Lax904597.Sat.satPosIn ![c, x] ∧ sharpVal μ x) ∨
      (RelMap Lax904597.Sat.satNegIn ![c, x] ∧ ¬sharpVal μ x) := by
  rcases sharpPt_cases c with ⟨c', rfl⟩ | ⟨i, u, rfl⟩
  · obtain ⟨x, hx⟩ := tseitin_clauses_of_realize B φ ha₀ μ hμ
      (fun y => sharpVal μ (sharpOldPt y)) (fun _ _ => Iff.rfl) c' ((sharp_isClause_old _).mp hc)
    rcases hx with ⟨hp, hv⟩ | ⟨hn, hv⟩
    · exact ⟨sharpOldPt x, Or.inl ⟨(sharp_lit_old Lax904597.Sat.satPosIn c' x).mpr hp, hv⟩⟩
    · exact ⟨sharpOldPt x, Or.inr ⟨(sharp_lit_old Lax904597.Sat.satNegIn c' x).mpr hn, hv⟩⟩
  · have hu := (sharp_isClause_taut _ _).mp hc
    refine ⟨sharpOldPt (tseitinVarPt (Sum.inl i) u), ?_⟩
    by_cases hv : sharpVal μ (sharpOldPt (tseitinVarPt (Sum.inl i) u))
    · exact Or.inl ⟨(sharp_lit_taut_iff Lax904597.Sat.satPosIn i u _).mpr ⟨hu, rfl⟩, hv⟩
    · exact Or.inr ⟨(sharp_lit_taut_iff Lax904597.Sat.satNegIn i u _).mpr ⟨hu, rfl⟩, hv⟩

variable (B φ) in
/-- **Models of the interpreted instance are the assignments of the block
realizing the kernel**, bijectively: a model induces a block assignment through
canonical padding, and is recovered from it because gates determine the
position variables and every variable of the instance sits at a canonical
tuple. -/
noncomputable def sharpModelEquiv (A : Type) [L.Structure A] [LinearOrder A] {a₀ : A}
    (ha₀ : IsBot a₀) :
    {ν : (sharpTseitinInterp B φ).Map A → Prop //
        Lax366625.CountingSat.SatModel ((sharpTseitinInterp B φ).Map A) ν} ≃
      {μ : B.Assignment A // RealizeWith μ φ finZeroElim} where
  toFun ν := ⟨padAssign a₀ fun vt x => ν.1 (sharpOldPt (tseitinVarPt vt x)),
    (tseitin_gates_of_clauses B φ ha₀ (fun y => ν.1 (sharpOldPt y))
      (sharp_old_clauses ν.2.1)).2⟩
  invFun μ := ⟨fun e => sharpVal μ.1 e ∧ Lax366625.CountingSat.SatOccurs ((sharpTseitinInterp B φ).Map A) e,
    satModel_restrict (sharpVal_clauses ha₀ μ.1 μ.2)⟩
  left_inv := by
    rintro ⟨ν, hν⟩
    refine Subtype.ext (funext fun e => propext ?_)
    have hg := (tseitin_gates_of_clauses B φ ha₀ (fun y => ν (sharpOldPt y))
      (sharp_old_clauses hν.1)).1
    change sharpVal (padAssign a₀ fun vt x => ν (sharpOldPt (tseitinVarPt vt x))) e ∧
      Lax366625.CountingSat.SatOccurs ((sharpTseitinInterp B φ).Map A) e ↔ ν e
    suffices h : Lax366625.CountingSat.SatOccurs ((sharpTseitinInterp B φ).Map A) e →
        (sharpVal (padAssign a₀ fun vt x => ν (sharpOldPt (tseitinVarPt vt x))) e ↔ ν e) from
      ⟨fun ⟨hv, ho⟩ => (h ho).mp hv, fun hv => ⟨(h (hν.2 e hv)).mpr hv, hν.2 e hv⟩⟩
    intro ho
    obtain ⟨vt, x, rfl, hcan⟩ := sharp_occurs_canon ho
    rw [sharpVal_varPt]
    rcases vt with i | ⟨m, p⟩
    · have hx := pad_pref_of_canon ha₀ (arity_le_tseitinDim B φ i) hcan
      exact iff_of_eq (congrArg (fun y => ν (sharpOldPt (tseitinVarPt (Sum.inl i) y))) hx)
    · have hm : m ≤ tseitinDim B φ := (nodeAt_le_maxCtx φ p).trans (maxCtx_le_tseitinDim B φ)
      have hx := pad_pref_of_canon ha₀ hm hcan
      refine (gates_unique _ φ _ hg m p (pref hm x)).symm.trans ?_
      exact iff_of_eq (congrArg (fun y => ν (sharpOldPt (tseitinVarPt (Sum.inr ⟨m, p⟩) y))) hx)
  right_inv := by
    rintro ⟨μ, hμ⟩
    refine Subtype.ext ?_
    refine Eq.trans ?_ (padAssign_tseitinVal B φ a₀ μ)
    funext i a
    exact propext (and_iff_left (sharp_occurs_block i (canon_pad ha₀ _ a)))

end Models

/-! ### Correctness of the reduction -/

/-- Realization of the kernel in the expansion by an assignment is
`DescriptiveComplexity.Tseitin.RealizeWith`. -/
theorem realize_iff_realizeWith {A : Type} [L.Structure A] (μ : B.Assignment A) :
    @Sentence.Realize (L.sum B.lang) A (@sumStructure L B.lang A _ (B.structure μ)) φ ↔
      RealizeWith μ φ finZeroElim :=
  iff_of_eq (congrArg₂
    (fun (v : Empty → A) (xs : Fin 0 → A) =>
      @BoundedFormula.Realize _ A (assignStructure L μ) _ _ φ v xs)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _))

/-- **Correctness of the parsimonious Tseitin interpretation**: the interpreted
CNF instance has as many models as the kernel has witnesses. -/
theorem sharpSat_sharpTseitin (A : Type) [L.Structure A] [LinearOrder A] [Finite A]
    [Nonempty A] :
    SharpSAT ((sharpTseitinInterp B φ).Map A) = Lax366625.WitnessCounting.witnessCount B φ A := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  rw [sharpSat_apply]
  exact (Nat.card_congr (sharpModelEquiv B φ A ha₀)).trans
    (Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun μ =>
      (realize_iff_realizeWith B φ μ).symm))

end Interp

/-! ### The counting Cook–Levin theorem -/

section Reduction

variable {L : Language.{0, 0}}

/-- The vocabulary map identifying the two order symbols of a doubly ordered
expansion. The kernel of a `#P` definition reads the order of the instance as
part of its vocabulary, and the Tseitin interpretation reads it again to pad
its tuples; both are the one order of the instance. -/
def orderCollapse (L : Language.{0, 0}) :
    (L.sum Language.order).sum Language.order →ᴸ L.sum Language.order :=
  LHom.sumElim (LHom.id _) LHom.sumInr

instance orderCollapse_isExpansionOn (A : Type) [L.Structure A] [LinearOrder A] :
    (orderCollapse L).IsExpansionOn A where
  map_onFunction := fun {n} f x => by
    rcases f with f | f
    · rfl
    · exact isEmptyElim f
  map_onRelation := fun {n} r x => by
    rcases r with r | r <;> rfl

end Reduction

end Lax175070Proofs.DescriptiveComplexity


