/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Problems.HornSat.Number
import Lax366625Proofs.DescriptiveComplexity.Problems.HornSat.Hardness
import Lax366625Proofs.DescriptiveComplexity.Problems.CircuitNumber.Hardness
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

namespace Lax366625.HornNumbers
end Lax366625.HornNumbers

namespace Lax366625.QuantitativeLogic
end Lax366625.QuantitativeLogic

namespace Lax366625Proofs.DescriptiveComplexity.DigitDefinable
end Lax366625Proofs.DescriptiveComplexity.DigitDefinable

namespace Lax366625Proofs.DescriptiveComplexity.DigitLFPDef
end Lax366625Proofs.DescriptiveComplexity.DigitLFPDef

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.HornSat
end Lax535992.HornSat

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax904597.Interpretations
end Lax904597.Interpretations

namespace Lax904597.Sat
end Lax904597.Sat

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.QuantitativeLogic (DigitDefinable DigitLFPDef)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.HornNumbers (Forced ForcedIn VarOrder hnBelow hnOut hornNumber)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Interpretations (FOInterpretation)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax485149.SecondOrderAtoms (SOAtom)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornProgram)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (Derives lfpAssign)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.HornSat (HornSatisfiable)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (orank)
end Lax366625Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax366625.HornNumbers (satOut)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax904597.Sat (sat)
end FirstOrder.Language

/-!
# Every digit-definable function reduces to the number written by unit propagation

`DescriptiveComplexity.DigitLFPDef.orderedParsimoniousHorn`: a function whose
binary digits are relations of a least fixed point
(`DescriptiveComplexity.DigitDefinable`) reduces to
`DescriptiveComplexity.HornNumber` by an ordered parsimonious reduction.

The Horn formula is the one of the Horn discharge
(`DescriptiveComplexity.hornInterp`): a variable per atom, a clause per
instance of a rule whose guard holds. Its least model is the least fixed point
of the rules (`DescriptiveComplexity.HornNum.forced_var_iff`), so the output
variables are the atoms of the relations holding the digits. The rules without
a head derive nothing and are dropped first: they would be goal clauses, and
could make the formula unsatisfiable.
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure CircNum

namespace HornNum

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

/-! ### Dropping the rules without a head -/

/-- The rules with a head. -/
def headed (prog : Lax535992.HornFragment.HornProgram (L.sum Language.order) B k) :
    Lax535992.HornFragment.HornProgram (L.sum Language.order) B k :=
  prog.filter fun c => c.head.isSome

theorem derives_headed {A : Type} [L.Structure A] [LinearOrder A]
    (prog : Lax535992.HornFragment.HornProgram (L.sum Language.order) B k) (q : Σ i : B.ι, Fin (B.arity i) → A) :
    Lax535992.LeastFixedPoint.Derives (headed prog) q ↔ Lax535992.LeastFixedPoint.Derives prog q := by
  constructor
  · intro h
    induction h with
    | @rule c hc a ha v hg _ ih => exact .rule (List.mem_of_mem_filter hc) ha hg ih
  · intro h
    induction h with
    | @rule c hc a ha v hg _ ih =>
      exact .rule (List.mem_filter.mpr ⟨hc, by rw [ha]; rfl⟩) ha hg ih

/-! ### The least model of the Horn formula is the least fixed point -/

section Forced

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

variable {prog : Lax535992.HornFragment.HornProgram (L.sum Language.order) B k}

omit [Finite A] [Nonempty A] in
/-- **Every forced variable is a derived atom**, canonically padded. -/
theorem derives_of_forcedIn {a₀ : A} (h₀ : IsBot a₀) :
    ∀ (n : ℕ) (i : B.ι) (w : Fin (clauseDim B k) → A),
      Lax366625.HornNumbers.ForcedIn (A := (hornInterp prog).Map A) n (varTag i, w) →
        Canon (B.arity i) w ∧ Lax535992.LeastFixedPoint.Derives prog ⟨i, pref (arity_le_clauseDim (k := k) i) w⟩ := by
  intro n
  induction n with
  | zero => exact fun _ _ h => h.elim
  | succ n ih =>
    rintro i w ⟨⟨tc, u⟩, hc, hp, hneg⟩
    rcases tc with (c | i') | ⟨⟩
    · obtain ⟨hguard, -⟩ := (horn_isClause_cl c u).mp hc
      obtain ⟨a, ha, rfl, hpad⟩ := (horn_posIn_cl_var c i u w).mp hp
      refine ⟨hpad.1, ?_⟩
      have hbody : ∀ b ∈ (clauseAt prog c).body,
          Lax535992.LeastFixedPoint.Derives prog ⟨b.idx, fun q => pref (le_clauseDim (B := B)) u (b.args q)⟩ := by
        intro b hb
        have hn := hneg ((varTag b.idx : HornTag prog), pad a₀ fun j => u (atomIdx b j))
          ((horn_negIn_cl_var c b.idx u _).mpr ⟨b, hb, rfl, padTup_pad h₀ _ u⟩)
        have := (ih b.idx _ hn).2
        rwa [pref_pad] at this
      rw [pref_eq_of_padTup hpad]
      exact Lax535992.LeastFixedPoint.Derives.rule (List.getElem_mem c.isLt) (Option.mem_def.mp ha) hguard hbody
    · exact absurd hc (horn_not_isClause_var i' u)
    · exact absurd hc (horn_not_isClause_junk u)

omit [Nonempty A] in
/-- **Every derived atom is a forced variable.** -/
theorem forced_of_derives {a₀ : A} (h₀ : IsBot a₀) :
    ∀ q : Σ i : B.ι, Fin (B.arity i) → A, Lax535992.LeastFixedPoint.Derives prog q →
      Lax366625.HornNumbers.Forced (A := (hornInterp prog).Map A) (varTag q.1, pad a₀ q.2) := by
  intro q h
  have := (hornInterp prog).map_finite A
  induction h with
  | @rule c hc a ha v hg _ ih =>
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hc
    have hu : ∀ b : Lax485149.SecondOrderAtoms.SOAtom B k,
        (fun q => pad (D := clauseDim B k) a₀ v (atomIdx b q)) = fun q => v (b.args q) :=
      fun b => funext fun q => pad_castLE a₀ le_clauseDim v (b.args q)
    refine ⟨Nat.card ((hornInterp prog).Map A) + 1,
      ((clTag ⟨n, hn⟩ : HornTag prog), pad a₀ v), ?_, ?_, ?_⟩
    · refine (horn_isClause_cl ⟨n, hn⟩ (pad a₀ v)).mpr ⟨?_, canon_pad h₀ k v⟩
      rw [show (fun j => pad (D := clauseDim B k) a₀ v (Fin.castLE le_clauseDim j)) = v from
        pref_pad a₀ le_clauseDim v]
      exact hg
    · refine (horn_posIn_cl_var ⟨n, hn⟩ a.idx (pad a₀ v) _).mpr
        ⟨a, Option.mem_def.mpr ha, rfl, ?_⟩
      rw [← hu a]
      exact padTup_pad h₀ (atomIdx a) (pad a₀ v)
    · rintro ⟨ty, wy⟩ hy
      rcases ty with (c' | i') | ⟨⟩
      · exact hy.elim
      · obtain ⟨b, hb, rfl, hpad⟩ := (horn_negIn_cl_var ⟨n, hn⟩ i' (pad a₀ v) wy).mp hy
        have := forced_forcedIn_card (ih b hb)
        rwa [eq_pad_of_padTup h₀ hpad, hu b]
      · exact hy.elim

omit [Nonempty A] in
/-- **The least model of the Horn formula is the least fixed point of the
rules.** -/
theorem forced_var_iff {a₀ : A} (h₀ : IsBot a₀) (i : B.ι) (w : Fin (clauseDim B k) → A) :
    Lax366625.HornNumbers.Forced (A := (hornInterp prog).Map A) (varTag i, w) ↔
      Canon (B.arity i) w ∧ Lax535992.LeastFixedPoint.Derives prog ⟨i, pref (arity_le_clauseDim (k := k) i) w⟩ := by
  constructor
  · rintro ⟨n, hn⟩
    exact derives_of_forcedIn h₀ n i w hn
  · rintro ⟨hc, hd⟩
    have := forced_of_derives h₀ _ hd
    rwa [pad_pref_of_canon h₀ (arity_le_clauseDim i) hc] at this

/-- **A Horn formula drawn from rules with heads is satisfiable.** -/
theorem hornSatisfiable_of_headed (hhead : ∀ c ∈ prog, c.head.isSome) :
    Lax535992.HornSat.HornSatisfiable ((hornInterp prog).Map A) := by
  obtain ⟨a₀, h₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  refine ⟨horn_atMostOnePositive prog, fun _ => True, ?_⟩
  rintro ⟨tc, u⟩ hc
  rcases tc with (c | i) | ⟨⟩
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hhead _ (List.getElem_mem c.isLt))
    exact ⟨((varTag a.idx : HornTag prog), pad a₀ fun j => u (atomIdx a j)),
      Or.inl ⟨(horn_posIn_cl_var c a.idx u _).mpr ⟨a, ha, rfl, padTup_pad h₀ _ u⟩, trivial⟩⟩
  · exact absurd hc (horn_not_isClause_var i u)
  · exact absurd hc (horn_not_isClause_junk u)

end Forced

/-! ### The interpretation, with its outputs -/

open Classical in
/-- **The Horn formula of a system of rules**, with the atoms of the relation
variables `bit τ` as output variables. -/
noncomputable def hornNumInterp (prog : Lax535992.HornFragment.HornProgram (L.sum Language.order) B k) {c : ℕ}
    (bit : Fin c → B.ι) :
    Lax904597.Interpretations.FOInterpretation (L.sum Language.order) Lax366625.HornNumbers.satOut (HornTag prog) (clauseDim B k) where
  relFormula {n} R :=
    match R with
    | Sum.inl r => (hornInterp prog).relFormula r
    | Sum.inr s =>
      match n, s with
      | _, .out => fun t =>
          match t 0 with
          | Sum.inl (Sum.inr i) =>
              if ∃ τ, bit τ = i then canonF (B.arity i) fun j => ((0 : Fin 1), j) else ⊥
          | _ => ⊥
      | _, .below => fun t =>
          match t 0, t 1 with
          | Sum.inl (Sum.inr i), Sum.inl (Sum.inr i') =>
              if ∃ τ τ', bit τ = i ∧ bit τ' = i' ∧ τ < τ' then ⊤
              else if i = i' then lexTupleLeF L (clauseDim B k) else ⊥
          | _, _ => ⊥

section Count

variable {A : Type} [L.Structure A] [LinearOrder A]

variable {prog : Lax535992.HornFragment.HornProgram (L.sum Language.order) B k} {c : ℕ} {bit : Fin c → B.ι}

/-- The CNF part of the interpreted structure is the Horn discharge's. -/
def satEquiv (prog : Lax535992.HornFragment.HornProgram (L.sum Language.order) B k) (bit : Fin c → B.ι) (A : Type)
    [L.Structure A] [LinearOrder A] :
    (hornNumInterp prog bit).Map A ≃[Lax904597.Sat.sat] (hornInterp prog).Map A :=
  ⟨Equiv.refl _, fun {_} f _ => isEmptyElim f, fun {_} _ _ => Iff.rfl⟩

open Classical in
theorem out_var (i : B.ι) (w : Fin (clauseDim B k) → A) :
    RelMap (M := (hornNumInterp prog bit).Map A) Lax366625.HornNumbers.hnOut ![(varTag i, w)] ↔
      (∃ τ, bit τ = i) ∧ Canon (B.arity i) w := by
  rw [FOInterpretation.relMap_map]
  exact (realize_ite_bot _ _ _).trans (and_congr Iff.rfl realize_canonF)

theorem not_out_cl (ci : Fin prog.length) (w : Fin (clauseDim B k) → A) :
    ¬RelMap (M := (hornNumInterp prog bit).Map A) Lax366625.HornNumbers.hnOut ![(clTag ci, w)] :=
  fun h => h.elim

theorem not_out_junk (w : Fin (clauseDim B k) → A) :
    ¬RelMap (M := (hornNumInterp prog bit).Map A) Lax366625.HornNumbers.hnOut ![((Sum.inr () : HornTag prog), w)] :=
  fun h => h.elim

open Classical in
theorem below_bit_bit (hinj : Function.Injective bit) (τ τ' : Fin c)
    (w w' : Fin (clauseDim B k) → A) :
    RelMap (M := (hornNumInterp prog bit).Map A) Lax366625.HornNumbers.hnBelow
        ![(varTag (bit τ), w), (varTag (bit τ'), w')] ↔
      τ < τ' ∨ (τ = τ' ∧ tupLeLex w w') := by
  rw [FOInterpretation.relMap_map]
  change (if ∃ σ σ', bit σ = bit τ ∧ bit σ' = bit τ' ∧ σ < σ' then ⊤
    else if bit τ = bit τ' then lexTupleLeF L (clauseDim B k) else ⊥ :
      (L.sum Language.order).Formula (Fin 2 × Fin (clauseDim B k))).Realize _ ↔ _
  have hex : (∃ σ σ', bit σ = bit τ ∧ bit σ' = bit τ' ∧ σ < σ') ↔ τ < τ' :=
    ⟨fun ⟨σ, σ', h1, h2, h3⟩ => hinj h1 ▸ hinj h2 ▸ h3, fun h => ⟨τ, τ', rfl, rfl, h⟩⟩
  by_cases hlt : τ < τ'
  · rw [if_pos (hex.mpr hlt)]
    exact iff_of_true (Formula.realize_top.mpr trivial) (Or.inl hlt)
  · rw [if_neg (fun h => hlt (hex.mp h))]
    refine (realize_ite_bot _ _ _).trans ⟨fun h => Or.inr ⟨hinj h.1, realize_lexTupleLeF.mp h.2⟩,
      fun h => h.elim (fun h' => absurd h' hlt)
        fun h' => ⟨congrArg bit h'.1, realize_lexTupleLeF.mpr h'.2⟩⟩

variable {ℓ : ℕ} {a₀ : A}

variable (prog bit) in
/-- The output variable of a position. -/
noncomputable def varPt (hℓ : ∀ τ, B.arity (bit τ) = ℓ) (a₀ : A)
    (q : Fin c ×ₗ Lex (Fin ℓ → A)) : (hornNumInterp prog bit).Map A :=
  (varTag (bit (ofLex q).1), pad a₀ fun n => ofLex (ofLex q).2 (Fin.cast (hℓ (ofLex q).1) n))

variable (hinj : Function.Injective bit) (hℓ : ∀ τ, B.arity (bit τ) = ℓ)

omit [L.Structure A] [LinearOrder A] in
include hinj in
theorem varPt_injective (a₀ : A) : Function.Injective (varPt prog bit hℓ a₀) := by
  rintro ⟨τ, y⟩ ⟨τ', y'⟩ h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  obtain rfl : τ = τ' := hinj (Sum.inr.inj (Sum.inl.inj h1))
  have h3 := pad_injective a₀ (arity_le_clauseDim (bit τ)) h2
  have : y = y' := funext fun n => congrFun h3 (Fin.cast (hℓ τ).symm n)
  rw [this]

theorem out_iff_varPt (h₀ : IsBot a₀) (p : (hornNumInterp prog bit).Map A) :
    RelMap (M := (hornNumInterp prog bit).Map A) Lax366625.HornNumbers.hnOut ![p] ↔
      ∃ q, p = varPt prog bit hℓ a₀ q := by
  obtain ⟨t, w⟩ := p
  rcases t with (ci | i) | ⟨⟩
  · refine iff_of_false (not_out_cl ci w) ?_
    rintro ⟨q, hq⟩
    exact absurd (Prod.mk.inj hq).1 (by simp)
  · rw [out_var]
    constructor
    · rintro ⟨⟨τ, rfl⟩, hc⟩
      exact ⟨toLex (τ, toLex fun n =>
          pref (arity_le_clauseDim (k := k) (bit τ)) w (Fin.cast (hℓ τ).symm n)),
        congrArg (Prod.mk _) (pad_pref_of_canon h₀ (arity_le_clauseDim (bit τ)) hc).symm⟩
    · rintro ⟨q, hq⟩
      obtain ⟨hi, hw⟩ := Prod.mk.inj hq
      obtain rfl := Sum.inr.inj (Sum.inl.inj hi)
      exact ⟨⟨_, rfl⟩, hw ▸ canon_pad h₀ _ _⟩
  · refine iff_of_false (not_out_junk w) ?_
    rintro ⟨q, hq⟩
    exact absurd (Prod.mk.inj hq).1 (by simp)

include hinj in
theorem below_varPt (q' q : Fin c ×ₗ Lex (Fin ℓ → A)) :
    RelMap (M := (hornNumInterp prog bit).Map A) Lax366625.HornNumbers.hnBelow
        ![varPt prog bit hℓ a₀ q', varPt prog bit hℓ a₀ q] ↔ q' ≤ q := by
  obtain ⟨τ', y'⟩ := q'
  obtain ⟨τ, y⟩ := q
  refine (below_bit_bit hinj τ' τ _ _).trans (Iff.trans ?_ prodLex_le_iff.symm)
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, (tupLeLex_iff_le _ _).mp ((tupLeLex_cast (hℓ τ') _ _).mp
      ((tupLeLex_pad a₀ (arity_le_clauseDim (bit τ')) _ _).mp h))⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, (tupLeLex_pad a₀ (arity_le_clauseDim (bit τ')) _ _).mpr
      ((tupLeLex_cast (hℓ τ') _ _).mpr ((tupLeLex_iff_le _ _).mpr h))⟩

variable [Finite A] [Nonempty A]

omit [Nonempty A] in
/-- **An output variable is forced exactly when its atom is derived.** -/
theorem forced_varPt (h₀ : IsBot a₀) (q : Fin c ×ₗ Lex (Fin ℓ → A)) :
    Lax366625.HornNumbers.Forced (varPt prog bit hℓ a₀ q) ↔
      Lax535992.LeastFixedPoint.lfpAssign prog (bit (ofLex q).1)
        fun n => ofLex (ofLex q).2 (Fin.cast (hℓ (ofLex q).1) n) := by
  have h1 := forced_equiv (satEquiv prog bit A) (varPt prog bit hℓ a₀ q)
  have h2 := forced_var_iff (prog := prog) h₀ (bit (ofLex q).1)
    (pad a₀ fun n => ofLex (ofLex q).2 (Fin.cast (hℓ (ofLex q).1) n))
  refine h1.symm.trans (h2.trans ⟨fun h => ?_, fun h => ⟨canon_pad h₀ _ _, ?_⟩⟩)
  · have := h.2
    rwa [pref_pad] at this
  · rw [pref_pad]
    exact h

omit [Finite A] [Nonempty A] in
include hinj hℓ in
/-- The output variables of the Horn formula are linearly ordered. -/
theorem varOrder_hornNumInterp (h₀ : IsBot a₀) : Lax366625.HornNumbers.VarOrder ((hornNumInterp prog bit).Map A) :=
  enum_linear (fun x => RelMap (M := (hornNumInterp prog bit).Map A) Lax366625.HornNumbers.hnOut ![x])
    (fun y x => RelMap (M := (hornNumInterp prog bit).Map A) Lax366625.HornNumbers.hnBelow ![y, x])
    (varPt prog bit hℓ a₀) (out_iff_varPt hℓ h₀) (below_varPt hinj hℓ)

include hinj in
open Classical in
/-- **The Horn formula writes the number whose digits are the relations
`bit τ` of the least fixed point**, the rules having heads. -/
theorem hornNumber_hornNumInterp (hhead : ∀ c ∈ prog, c.head.isSome) (h₀ : IsBot a₀) :
    Lax366625.HornNumbers.hornNumber ((hornNumInterp prog bit).Map A) =
      ∑ᶠ q : Fin c ×ₗ Lex (Fin ℓ → A),
        if Lax535992.LeastFixedPoint.lfpAssign prog (bit (ofLex q).1)
            (fun n => ofLex (ofLex q).2 (Fin.cast (hℓ (ofLex q).1) n)) then 2 ^ Lax895169.BitPredicate.orank q
        else 0 := by
  have hs : Lax535992.HornSat.HornSatisfiable ((hornNumInterp prog bit).Map A) :=
    (hornSatisfiable_iso (satEquiv prog bit A)).mpr (hornSatisfiable_of_headed hhead)
  rw [Lax366625.HornNumbers.hornNumber, if_pos ⟨hs, varOrder_hornNumInterp hinj hℓ h₀⟩]
  have key := finsum_digits_eq (X := (hornNumInterp prog bit).Map A)
    (fun x => RelMap Lax366625.HornNumbers.hnOut ![x]) Lax366625.HornNumbers.Forced (fun y x => RelMap Lax366625.HornNumbers.hnBelow ![y, x])
    (varPt prog bit hℓ a₀) (varPt_injective hinj hℓ a₀) (out_iff_varPt hℓ h₀)
    (below_varPt hinj hℓ)
  refine Eq.trans ?_ (key.trans ?_)
  · exact finsum_congr fun x => if_congr Iff.rfl rfl rfl
  · exact finsum_congr fun q => if_congr (forced_varPt hℓ h₀ q) rfl rfl

end Count

end HornNum

/-! ### The reduction -/

section Reduction

variable {L : Language.{0, 0}} [L.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L}

/-- **A function whose binary digits are relations of a least fixed point
reduces to the number written by unit propagation.** -/
noncomputable def DigitLFPDef.orderedParsimoniousHorn (d : Lax366625.QuantitativeLogic.DigitLFPDef L)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      C A = d.value A) : C ≤ᵖ[≤] HornNumber where
  Tag := HornTag (HornNum.headed d.rules)
  dim := clauseDim d.B d.k
  toInterpretation := HornNum.hornNumInterp (HornNum.headed d.rules) d.bit
  correct := fun A _ _ _ _ => by
    classical
    obtain ⟨a₀, h₀⟩ := Finite.exists_min (id : A → A)
    refine (h A).trans (Eq.trans ?_ (HornNum.hornNumber_hornNumInterp (a₀ := a₀)
      d.bit_injective d.arity_bit (fun c hc => (List.mem_filter.mp hc).2) h₀).symm)
    exact finsum_congr fun q => if_congr
      (HornNum.derives_headed d.rules ⟨_, _⟩).symm rfl rfl

end Reduction

end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.DigitLFPDef

export Lax366625Proofs.DescriptiveComplexity.DigitLFPDef (orderedParsimoniousHorn)

end Lax366625.QuantitativeLogic.DigitLFPDef

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure CircNum

section Reduction

variable {L : Language.{0, 0}} [L.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L}

/-- **Every digit-definable problem parsimoniously reduces to the number
written by unit propagation.** -/
theorem DigitDefinable.nonempty_orderedParsimoniousHorn (h : Lax366625.QuantitativeLogic.DigitDefinable C) :
    Nonempty (C ≤ᵖ[≤] HornNumber) := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d.orderedParsimoniousHorn hd⟩

end Reduction

end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.DigitDefinable

export Lax366625Proofs.DescriptiveComplexity.DigitDefinable (nonempty_orderedParsimoniousHorn)

end Lax366625.QuantitativeLogic.DigitDefinable

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure CircNum

section Reduction

variable {L : Language.{0, 0}} [L.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L}

end Reduction

end Lax366625Proofs.DescriptiveComplexity


