/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Problems.CircuitNumber.Draw
import Lax366625Proofs.DescriptiveComplexity.Counting.DigitDefinable
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

namespace Lax366625.NumberedCircuits
end Lax366625.NumberedCircuits

namespace Lax366625.QuantitativeLogic
end Lax366625.QuantitativeLogic

namespace Lax366625Proofs.DescriptiveComplexity.DigitDefinable
end Lax366625Proofs.DescriptiveComplexity.DigitDefinable

namespace Lax366625Proofs.DescriptiveComplexity.DigitLFPDef
end Lax366625Proofs.DescriptiveComplexity.DigitLFPDef

namespace Lax485149.SecondOrderAtoms
end Lax485149.SecondOrderAtoms

namespace Lax535992.CircuitValue
end Lax535992.CircuitValue

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax895169.BitPredicate
end Lax895169.BitPredicate

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.CountingProblems (CountingProblem)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.QuantitativeLogic (DigitDefinable DigitLFPDef)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.NumberedCircuits (OutBit OutOrder circuitNumber)
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
export Lax535992.CircuitValue (GateVal)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax895169.BitPredicate (orank)
end Lax366625Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax366625.NumberedCircuits (ncBelow ncOut)
end FirstOrder.Language

/-!
# Every digit-definable function reduces to the number written by a circuit

`DescriptiveComplexity.DigitLFPDef.orderedParsimonious`: a function whose binary
digits are relations of a least fixed point
(`DescriptiveComplexity.DigitDefinable`) reduces to
`DescriptiveComplexity.CircuitNumber` by an ordered parsimonious reduction, the
circuit being the one drawn from the rules
(`DescriptiveComplexity.CircNum.drawInterp`).

* **The circuit evaluates the fixed point**
  (`DescriptiveComplexity.CircNum.gateVal_atom_iff`): the gate of an atom
  derives `1` exactly when the rules derive the atom. One direction rebuilds a
  derivation of the rules as a derivation of the gates, link by link along a
  conjunction chain (`DescriptiveComplexity.CircNum.gateVal_of_derives`); the
  other inverts a derivation of the gates, every rule that can fire at a gate
  of the drawn circuit firing for the intended reason
  (`DescriptiveComplexity.CircNum.val_of_gateVal`).
* **The outputs are the digits**: the output gates are the canonically padded
  atoms of the relations holding the digits, and padding preserves the
  lexicographic order (`DescriptiveComplexity.CircNum.tupLeLex_pad`), so the
  outputs are compared as their positions are
  (`DescriptiveComplexity.CircNum.below_bitPt`), and the number is read off
  the positions (`DescriptiveComplexity.finsum_digits_eq`).
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

namespace CircNum

/-! ### Padding and the lexicographic order -/

section Pad

variable {A : Type} {D m : ℕ}

theorem pad_of_lt (a₀ : A) (w : Fin m → A) {j : Fin D} (hj : (j : ℕ) < m) :
    pad a₀ w j = w ⟨j, hj⟩ := by
  rw [pad, dif_pos hj]

theorem pad_of_le (a₀ : A) (w : Fin m → A) {j : Fin D} (hj : m ≤ (j : ℕ)) :
    pad a₀ w j = a₀ := by
  rw [pad, dif_neg (not_lt.mpr hj)]

theorem pad_castLE (a₀ : A) (h : m ≤ D) (w : Fin m → A) (j : Fin m) :
    pad a₀ w (Fin.castLE h j) = w j :=
  congrFun (pref_pad a₀ h w) j

theorem pad_injective (a₀ : A) (h : m ≤ D) :
    Function.Injective (pad (D := D) a₀ : (Fin m → A) → Fin D → A) := fun x y hxy => by
  rw [← pref_pad a₀ h x, ← pref_pad a₀ h y, hxy]

/-- **Padding preserves the lexicographic order.** -/
theorem tupLeLex_pad [LinearOrder A] (a₀ : A) (h : m ≤ D) (y x : Fin m → A) :
    tupLeLex (pad (D := D) a₀ y) (pad a₀ x) ↔ tupLeLex y x := by
  constructor
  · rintro (he | ⟨j, hj, hlt⟩)
    · exact Or.inl (pad_injective a₀ h he)
    · have hjm : (j : ℕ) < m := by
        by_contra hjm
        rw [pad_of_le a₀ y (not_lt.mp hjm), pad_of_le a₀ x (not_lt.mp hjm)] at hlt
        exact lt_irrefl _ hlt
      refine Or.inr ⟨⟨j, hjm⟩, fun i hi => ?_, ?_⟩
      · have := hj (Fin.castLE h i) hi
        rwa [pad_castLE, pad_castLE] at this
      · rwa [pad_of_lt a₀ y hjm, pad_of_lt a₀ x hjm] at hlt
  · rintro (rfl | ⟨j, hj, hlt⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨Fin.castLE h j, fun i hi => ?_, ?_⟩
      · have him : (i : ℕ) < m := lt_trans hi j.isLt
        rw [pad_of_lt a₀ y him, pad_of_lt a₀ x him]
        exact hj ⟨i, him⟩ hi
      · rwa [pad_castLE, pad_castLE]

end Pad

variable {L : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {k : ℕ}

variable {A : Type} [L.Structure A] [LinearOrder A]

variable {prog : Lax535992.HornFragment.HornProgram (L.sum Language.order) B k} {c : ℕ} {bit : Fin c → B.ι}

/-! ### What the gates derive -/

/-- What a gate deriving `1` means: an atom is canonically padded and derived
by the rules; a link of a conjunction chain has every body atom from its
position on derived. -/
def Val (p : (drawInterp prog bit).Map A) : Prop :=
  match p.1 with
  | Sum.inl i => Canon (B.arity i) p.2 ∧
      Lax535992.LeastFixedPoint.Derives prog ⟨i, pref (arity_le_clauseDim (k := k) i) p.2⟩
  | Sum.inr ⟨c, j⟩ => ∀ (n : ℕ) (a : Lax485149.SecondOrderAtoms.SOAtom B k), (j : ℕ) ≤ n →
      (clauseAt prog c).body[n]? = some a →
        Lax535992.LeastFixedPoint.Derives prog ⟨a.idx, fun q => p.2 (atomIdx a q)⟩

/-- An atom read through a canonically padded occurrence. -/
theorem pref_eq_of_padTup {a : Lax485149.SecondOrderAtoms.SOAtom B k} {u w : Fin (clauseDim B k) → A}
    (h : PadTup (atomIdx a) u w) :
    pref (arity_le_clauseDim (k := k) a.idx) w = fun q => u (atomIdx a q) :=
  funext fun q => h.2 (Fin.castLE (arity_le_clauseDim a.idx) q) q.isLt

/-- **Nothing else evaluates to `1`.** By induction on the derivation of the
gates: every rule that can fire at a gate of the drawn circuit fires for the
intended reason. The false rail carries no information and is not tracked. -/
theorem val_of_gateVal :
    ∀ {b : Bool} {p : (drawInterp prog bit).Map A}, Lax535992.CircuitValue.GateVal b p → b = true → Val p := by
  intro b p h
  induction h with
  | @constTrue g hg =>
    intro _
    obtain ⟨t, w⟩ := g
    rcases t with i | ⟨c, j⟩
    · exact (not_isTrue_atom i w hg).elim
    · intro n a hn ha
      have hlen : (clauseAt prog c).body.length ≤ n := ((isTrue_step c j w).mp hg) ▸ hn
      rw [List.getElem?_eq_none hlen] at ha
      exact absurd ha (by simp)
  | @constFalse g hg => simp
  | @andTrue g l r hg hl hr _ _ ihl ihr =>
    intro _
    obtain ⟨t, w⟩ := g
    rcases t with i | ⟨c, j⟩
    · exact (not_isAnd_atom i w hg).elim
    · obtain ⟨tl, wl⟩ := l
      rcases tl with il | ⟨cl, jl⟩
      swap
      · exact (not_left_step_step c cl j jl w wl hl).elim
      obtain ⟨a, ha, rfl, hpad⟩ := (left_step_atom c j w _ wl).mp hl
      have hcur : Lax535992.LeastFixedPoint.Derives prog ⟨a.idx, fun q => w (atomIdx a q)⟩ := by
        have := (ihl rfl).2
        rwa [pref_eq_of_padTup hpad] at this
      obtain ⟨tr, wr⟩ := r
      rcases tr with ir | ⟨cr, jr⟩
      · exact (not_right_step_atom c j w ir wr hr).elim
      obtain ⟨⟨rfl, hj⟩, rfl⟩ := (right_step_step c cr j jr w wr).mp hr
      intro n a' hn ha'
      rcases Nat.eq_or_lt_of_le hn with rfl | hlt
      · obtain rfl : a = a' := Option.some.inj (ha.symm.trans ha')
        exact hcur
      · exact ihr rfl n a' (hj ▸ hlt) ha'
  | @andFalseLeft g l hg hl _ ihl => simp
  | @andFalseRight g r hg hr _ ihr => simp
  | @orTrueLeft g l hg hl _ ihl =>
    intro _
    obtain ⟨t, w⟩ := g
    rcases t with i | ⟨c, j⟩
    swap
    · exact (not_isOr_step c j w hg).elim
    obtain ⟨tl, u⟩ := l
    rcases tl with il | ⟨c, j⟩
    · exact (not_left_atom_atom i il w u hl).elim
    obtain ⟨hj, hguard, a, ha, rfl, hpad⟩ := (left_atom_step _ w c j u).mp hl
    refine ⟨hpad.1, ?_⟩
    have hbody : ∀ b ∈ (clauseAt prog c).body,
        Lax535992.LeastFixedPoint.Derives prog ⟨b.idx, fun q => pref (le_clauseDim (B := B)) u (b.args q)⟩ := by
      intro b hb
      obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hb
      exact ihl rfl n b (hj ▸ Nat.zero_le n) hn
    rw [pref_eq_of_padTup hpad]
    exact Lax535992.LeastFixedPoint.Derives.rule (List.getElem_mem c.isLt) (Option.mem_def.mp ha) hguard hbody
  | @orTrueRight g r hg hr _ ihr =>
    intro _
    obtain ⟨t, w⟩ := g
    rcases t with i | ⟨c, j⟩
    · exact (not_right_atom i w r hr).elim
    · exact (not_isOr_step c j w hg).elim
  | @orFalse g l r hg hl hr _ _ ihl ihr => simp
  | @notTrue g i hg hi _ ihi => exact fun _ => (not_isNot g hg).elim
  | @notFalse g i hg hi _ ihi => simp

/-- **Every atom the rules derive has its gate deriving `1`**: a derivation of
the rules is rebuilt as a derivation of the gates, the conjunction chain of
each rule instance being climbed from its end. -/
theorem gateVal_of_derives {a₀ : A} (h₀ : IsBot a₀) :
    ∀ q : Σ i : B.ι, Fin (B.arity i) → A, Lax535992.LeastFixedPoint.Derives prog q →
      Lax535992.CircuitValue.GateVal (A := (drawInterp prog bit).Map A) true (atomTag q.1, pad a₀ q.2) := by
  intro q h
  induction h with
  | @rule c hc a ha v hg _ ih =>
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hc
    let ci : Fin prog.length := ⟨n, hn⟩
    let u : Fin (clauseDim B k) → A := pad a₀ v
    have hu : ∀ b : Lax485149.SecondOrderAtoms.SOAtom B k, (fun q => u (atomIdx b q)) = fun q => v (b.args q) :=
      fun b => funext fun q => pad_castLE a₀ le_clauseDim v (b.args q)
    -- the conjunction chain of this rule instance, climbed from its end
    have chain : ∀ (d n' : ℕ) (hn' : n' ≤ (clauseAt prog ci).body.length),
        (clauseAt prog ci).body.length - n' = d →
          Lax535992.CircuitValue.GateVal (A := (drawInterp prog bit).Map A) true
            (stepTag ci ⟨n', Nat.lt_succ_of_le hn'⟩, u) := by
      intro d
      induction d with
      | zero =>
        intro n' hn' hd
        exact .constTrue ((isTrue_step ci _ u).mpr (by simp only; omega))
      | succ d ihd =>
        intro n' hn' hd
        have hlt : n' < (clauseAt prog ci).body.length := by omega
        let b : Lax485149.SecondOrderAtoms.SOAtom B k := (clauseAt prog ci).body[n']
        have hb : (clauseAt prog ci).body[n']? = some b := List.getElem?_eq_getElem hlt
        refine .andTrue (l := (atomTag b.idx, pad a₀ fun q => v (b.args q)))
          (r := (stepTag ci ⟨n' + 1, Nat.succ_lt_succ hlt⟩, u))
          ((isAnd_step ci _ u).mpr hlt) ?_ ?_ (ih b (List.getElem_mem hlt))
          (ihd (n' + 1) hlt (by omega))
        · refine (left_step_atom ci _ u b.idx _).mpr ⟨b, hb, rfl, ?_⟩
          rw [← hu b]
          exact padTup_pad h₀ (atomIdx b) u
        · exact (right_step_step ci ci _ _ u u).mpr ⟨⟨rfl, rfl⟩, rfl⟩
    refine .orTrueLeft (l := (stepTag ci ⟨0, Nat.succ_pos _⟩, u)) (isOr_atom _ _) ?_
      (chain _ 0 (Nat.zero_le _) rfl)
    refine (left_atom_step a.idx _ ci _ u).mpr ⟨rfl, ?_, a, Option.mem_def.mpr ha, rfl, ?_⟩
    · rwa [pref_pad]
    · rw [← hu a]
      exact padTup_pad h₀ (atomIdx a) u

/-- **The circuit evaluates the fixed point**: the gate of an atom derives `1`
exactly when it is canonically padded and the rules derive the atom. -/
theorem gateVal_atom_iff {a₀ : A} (h₀ : IsBot a₀) (i : B.ι) (w : Fin (clauseDim B k) → A) :
    Lax535992.CircuitValue.GateVal (A := (drawInterp prog bit).Map A) true (atomTag i, w) ↔
      Canon (B.arity i) w ∧ Lax535992.LeastFixedPoint.Derives prog ⟨i, pref (arity_le_clauseDim (k := k) i) w⟩ := by
  refine ⟨fun h => val_of_gateVal h rfl, fun h => ?_⟩
  have := gateVal_of_derives (bit := bit) h₀ _ h.2
  rwa [pad_pref_of_canon h₀ (arity_le_clauseDim i) h.1] at this

/-! ### The outputs are the digits -/

section Count

variable {a₀ : A} {ℓ : ℕ}

omit [L.Structure A] in
/-- The lexicographic order does not depend on how the coordinates are
numbered. -/
theorem tupLeLex_cast {m : ℕ} (h : m = ℓ) (y x : Fin ℓ → A) :
    tupLeLex (fun k : Fin m => y (Fin.cast h k)) (fun k => x (Fin.cast h k)) ↔ tupLeLex y x := by
  subst h
  exact Iff.rfl

omit [L.Structure A] in
theorem tupLeLex_iff_le {m : ℕ} (y x : Fin m → A) : tupLeLex y x ↔ toLex y ≤ toLex x := by
  rw [le_iff_lt_or_eq, or_comm]
  exact or_congr ⟨fun h => congrArg toLex h, fun h => h⟩ Iff.rfl

variable (prog bit) in
/-- The output gate of a position: the atom of its tuple in the relation
variable of its group, canonically padded. -/
noncomputable def bitPt (hℓ : ∀ τ, B.arity (bit τ) = ℓ) (a₀ : A)
    (q : Fin c ×ₗ Lex (Fin ℓ → A)) : (drawInterp prog bit).Map A :=
  (atomTag (bit (ofLex q).1), pad a₀ fun k => ofLex (ofLex q).2 (Fin.cast (hℓ (ofLex q).1) k))

variable (hinj : Function.Injective bit) (hℓ : ∀ τ, B.arity (bit τ) = ℓ)

omit [L.Structure A] [LinearOrder A] in
include hinj in
theorem bitPt_injective (a₀ : A) : Function.Injective (bitPt prog bit hℓ a₀) := by
  rintro ⟨τ, y⟩ ⟨τ', y'⟩ h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  obtain rfl : τ = τ' := hinj (Sum.inl.inj h1)
  have h3 := pad_injective a₀ (arity_le_clauseDim (bit τ)) h2
  have : y = y' := funext fun k => congrFun h3 (Fin.cast (hℓ τ).symm k)
  rw [this]

/-- The output gates are the gates of the positions. -/
theorem out_iff_bitPt (h₀ : IsBot a₀) (p : (drawInterp prog bit).Map A) :
    RelMap (M := (drawInterp prog bit).Map A) Lax366625.NumberedCircuits.ncOut ![p] ↔ ∃ q, p = bitPt prog bit hℓ a₀ q := by
  obtain ⟨t, w⟩ := p
  rcases t with i | ⟨c', j⟩
  · rw [out_atom]
    constructor
    · rintro ⟨⟨τ, rfl⟩, hc⟩
      exact ⟨toLex (τ, toLex fun n =>
          pref (arity_le_clauseDim (k := k) (bit τ)) w (Fin.cast (hℓ τ).symm n)),
        congrArg (Prod.mk _) (pad_pref_of_canon h₀ (arity_le_clauseDim (bit τ)) hc).symm⟩
    · rintro ⟨q, hq⟩
      obtain ⟨hi, hw⟩ := Prod.mk.inj hq
      obtain rfl := Sum.inl.inj hi
      exact ⟨⟨_, rfl⟩, hw ▸ canon_pad h₀ _ _⟩
  · refine iff_of_false (not_out_step c' j w) ?_
    rintro ⟨q, hq⟩
    exact absurd (Prod.mk.inj hq).1 (by simp)

/-- **An output gate holds the digit of its position.** -/
theorem outBit_bitPt (h₀ : IsBot a₀) (q : Fin c ×ₗ Lex (Fin ℓ → A)) :
    Lax366625.NumberedCircuits.OutBit (bitPt prog bit hℓ a₀ q) ↔
      Lax535992.LeastFixedPoint.lfpAssign prog (bit (ofLex q).1)
        fun k => ofLex (ofLex q).2 (Fin.cast (hℓ (ofLex q).1) k) := by
  constructor
  · rintro ⟨-, hv⟩
    have := ((gateVal_atom_iff h₀ (bit (ofLex q).1) _).mp hv).2
    rwa [pref_pad] at this
  · intro h
    exact ⟨(out_atom _ _).mpr ⟨⟨_, rfl⟩, canon_pad h₀ _ _⟩, gateVal_of_derives h₀ ⟨_, _⟩ h⟩

include hinj in
/-- The gates of the positions are compared as the positions are. -/
theorem below_bitPt (q' q : Fin c ×ₗ Lex (Fin ℓ → A)) :
    RelMap (M := (drawInterp prog bit).Map A) Lax366625.NumberedCircuits.ncBelow
        ![bitPt prog bit hℓ a₀ q', bitPt prog bit hℓ a₀ q] ↔ q' ≤ q := by
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

include hinj hℓ in
/-- The outputs of the drawn circuit are linearly ordered. -/
theorem outOrder_drawInterp (h₀ : IsBot a₀) : Lax366625.NumberedCircuits.OutOrder ((drawInterp prog bit).Map A) :=
  enum_linear (fun x => RelMap (M := (drawInterp prog bit).Map A) Lax366625.NumberedCircuits.ncOut ![x])
    (fun y x => RelMap (M := (drawInterp prog bit).Map A) Lax366625.NumberedCircuits.ncBelow ![y, x])
    (bitPt prog bit hℓ a₀) (out_iff_bitPt hℓ h₀) (below_bitPt hinj hℓ)

include hinj in
open Classical in
/-- **The drawn circuit writes the number whose digits are the relations
`bit τ` of the least fixed point.** -/
theorem circuitNumber_drawInterp [Finite A] (h₀ : IsBot a₀) :
    Lax366625.NumberedCircuits.circuitNumber ((drawInterp prog bit).Map A) =
      ∑ᶠ q : Fin c ×ₗ Lex (Fin ℓ → A),
        if Lax535992.LeastFixedPoint.lfpAssign prog (bit (ofLex q).1)
            (fun k => ofLex (ofLex q).2 (Fin.cast (hℓ (ofLex q).1) k)) then 2 ^ Lax895169.BitPredicate.orank q
        else 0 := by
  rw [Lax366625.NumberedCircuits.circuitNumber, if_pos (outOrder_drawInterp hinj hℓ h₀)]
  have key := finsum_digits_eq (X := (drawInterp prog bit).Map A)
    (fun x => RelMap Lax366625.NumberedCircuits.ncOut ![x]) (Lax535992.CircuitValue.GateVal true) (fun y x => RelMap Lax366625.NumberedCircuits.ncBelow ![y, x])
    (bitPt prog bit hℓ a₀) (bitPt_injective hinj hℓ a₀) (out_iff_bitPt hℓ h₀)
    (below_bitPt hinj hℓ)
  refine Eq.trans ?_ (key.trans ?_)
  · exact finsum_congr fun x => if_congr Iff.rfl rfl rfl
  · refine finsum_congr fun q => if_congr ⟨fun hg => ?_, fun h => ((outBit_bitPt hℓ h₀ q).mpr h).2⟩
      rfl rfl
    exact (outBit_bitPt hℓ h₀ q).mp ⟨(out_iff_bitPt hℓ h₀ _).mpr ⟨q, rfl⟩, hg⟩

end Count

end CircNum

/-! ### The reduction -/

section Reduction

variable {L : Language.{0, 0}} [L.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L}

/-- **A function whose binary digits are relations of a least fixed point
reduces to the number written by a circuit**, by drawing the circuit of the
rules inside the instance. -/
noncomputable def DigitLFPDef.orderedParsimonious (d : Lax366625.QuantitativeLogic.DigitLFPDef L)
    (h : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      C A = d.value A) : C ≤ᵖ[≤] CircuitNumber where
  Tag := CircNum.DrawTag d.rules
  tagNonempty := ⟨Sum.inl (d.bit ⟨0, d.c_pos⟩)⟩
  dim := clauseDim d.B d.k
  toInterpretation := CircNum.drawInterp d.rules d.bit
  correct := fun A _ _ _ _ => by
    obtain ⟨a₀, h₀⟩ := Finite.exists_min (id : A → A)
    exact (h A).trans
      (CircNum.circuitNumber_drawInterp (a₀ := a₀) d.bit_injective d.arity_bit h₀).symm

end Reduction

end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.DigitLFPDef

export Lax366625Proofs.DescriptiveComplexity.DigitLFPDef (orderedParsimonious)

end Lax366625.QuantitativeLogic.DigitLFPDef

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Reduction

variable {L : Language.{0, 0}} [L.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L}

/-- **Every digit-definable problem parsimoniously reduces to the number
written by a circuit.** -/
theorem DigitDefinable.nonempty_orderedParsimonious (h : Lax366625.QuantitativeLogic.DigitDefinable C) :
    Nonempty (C ≤ᵖ[≤] CircuitNumber) := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d.orderedParsimonious hd⟩

end Reduction

end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625.QuantitativeLogic.DigitDefinable

export Lax366625Proofs.DescriptiveComplexity.DigitDefinable (nonempty_orderedParsimonious)

end Lax366625.QuantitativeLogic.DigitDefinable

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Reduction

variable {L : Language.{0, 0}} [L.IsRelational] {C : Lax366625.CountingProblems.CountingProblem L}

end Reduction

end Lax366625Proofs.DescriptiveComplexity


