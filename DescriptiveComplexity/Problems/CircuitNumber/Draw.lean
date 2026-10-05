/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CircuitNumber.Defs
import DescriptiveComplexity.Problems.HornSat.Hardness
import DescriptiveComplexity.OrderedComposition

/-!
# The circuit of a system of rules

A system of rules (`DescriptiveComplexity.HornProgram`) over an ordered
structure is drawn as a monotone circuit whose gates evaluate its least fixed
point: `DescriptiveComplexity.CircNum.drawInterp`.

* One **disjunction** gate per relation variable `i` and per tuple, canonically
  padded (`DescriptiveComplexity.Padding`): the atom `i(x̄)`. Its inputs – all
  on the `left` wire, a disjunction of the circuit vocabulary being true as
  soon as *some* gate wired to its left is – are the rule instances deriving
  it: the rules whose head is that atom, at the valuations satisfying their
  guard. The guard is a formula of the input vocabulary, so it is evaluated by
  the *wiring*, not by the circuit.
* One **conjunction chain** per rule `c` and per valuation `v̄` of its
  variables: the gate `(c, j, v̄)` is the conjunction of the `j`-th body atom,
  at `v̄`, and of the gate `(c, j + 1, v̄)`; past the last body atom, the gate
  is the constant `1`. So `(c, 0, v̄)` is “every body atom of `c` holds at
  `v̄`”.
* The **outputs** are the atoms of the relation variables `bit τ`, compared
  first by `τ`, then lexicographically.

Nothing is stratified by stages: the circuit may have cycles, and the
evaluation of `DescriptiveComplexity.GateVal`, a least derivation, is the
least fixed point of the rules as it stands.

This file holds the interpretation and reads its relations; the evaluation is
`DescriptiveComplexity.Problems.CircuitNumber.Hardness`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace CircNum

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ}

/-! ### Tags -/

/-- The tags of the drawing: one per relation variable, for the atoms, and one
per rule and position in its body, for the conjunction chains. -/
abbrev DrawTag (prog : HornProgram (L.sum Language.order) B k) : Type :=
  B.ι ⊕ (Σ c : Fin prog.length, Fin ((clauseAt prog c).body.length + 1))

/-- The tag of the atoms of the relation variable `i`. -/
abbrev atomTag {prog : HornProgram (L.sum Language.order) B k} (i : B.ι) : DrawTag prog :=
  Sum.inl i

/-- The tag of the `j`-th link of the conjunction chains of the rule `c`. -/
abbrev stepTag {prog : HornProgram (L.sum Language.order) B k} (c : Fin prog.length)
    (j : Fin ((clauseAt prog c).body.length + 1)) : DrawTag prog :=
  Sum.inr ⟨c, j⟩

/-! ### The interpretation -/

open Classical in
/-- **The circuit of a system of rules**, drawn inside an ordered structure,
with the atoms of the relation variables `bit τ` as outputs. -/
noncomputable def drawInterp (prog : HornProgram (L.sum Language.order) B k) {c : ℕ}
    (bit : Fin c → B.ι) :
    FOInterpretation (L.sum Language.order) Language.numCircuit (DrawTag prog)
      (clauseDim B k) where
  relFormula {n} R :=
    match n, R with
    | _, .isTrue => fun t =>
        match t 0 with
        | Sum.inr ⟨c, j⟩ => if (j : ℕ) = (clauseAt prog c).body.length then ⊤ else ⊥
        | _ => ⊥
    | _, .isFalse => fun _ => ⊥
    | _, .isAnd => fun t =>
        match t 0 with
        | Sum.inr ⟨c, j⟩ => if (j : ℕ) < (clauseAt prog c).body.length then ⊤ else ⊥
        | _ => ⊥
    | _, .isOr => fun t =>
        match t 0 with
        | Sum.inl _ => ⊤
        | _ => ⊥
    | _, .isNot => fun _ => ⊥
    | _, .out => fun t =>
        match t 0 with
        | Sum.inl i =>
            if ∃ τ, bit τ = i then canonF (B.arity i) fun j => ((0 : Fin 1), j) else ⊥
        | _ => ⊥
    | _, .left => fun t =>
        match t 0, t 1 with
        | Sum.inl i, Sum.inr ⟨c, j⟩ =>
            if (j : ℕ) = 0 then
              guardF (clauseAt prog c).guard (fun j => ((1 : Fin 2), j)) ⊓
                headOccF (clauseAt prog c) i (fun j => ((1 : Fin 2), j))
                  fun j => ((0 : Fin 2), j)
            else ⊥
        | Sum.inr ⟨c, j⟩, Sum.inl i =>
            ((clauseAt prog c).body[(j : ℕ)]?).elim ⊥ fun a =>
              if a.idx = i then
                atomOccF a (fun j => ((0 : Fin 2), j)) fun j => ((1 : Fin 2), j)
              else ⊥
        | _, _ => ⊥
    | _, .right => fun t =>
        match t 0, t 1 with
        | Sum.inr ⟨c, j⟩, Sum.inr ⟨c', j'⟩ =>
            if c = c' ∧ (j' : ℕ) = j + 1 then
              eqTupF (fun j => ((0 : Fin 2), j)) fun j => ((1 : Fin 2), j)
            else ⊥
        | _, _ => ⊥
    | _, .below => fun t =>
        match t 0, t 1 with
        | Sum.inl i, Sum.inl i' =>
            if ∃ τ τ', bit τ = i ∧ bit τ' = i' ∧ τ < τ' then ⊤
            else if i = i' then lexTupleLeF L (clauseDim B k) else ⊥
        | _, _ => ⊥

/-! ### Reading the relations -/

section Read

variable {A : Type} [L.Structure A] [LinearOrder A]
variable {prog : HornProgram (L.sum Language.order) B k} {c : ℕ} {bit : Fin c → B.ι}

omit [LinearOrder A] in
/-- A formula present under a condition. -/
theorem realize_ite_bot {L' : Language.{0, 0}} [L'.Structure A] {α : Type} (p : Prop)
    [Decidable p] (φ : L'.Formula α) (v : α → A) :
    (if p then φ else ⊥).Realize v ↔ p ∧ φ.Realize v := by
  split_ifs with h
  · exact (and_iff_right h).symm
  · exact iff_of_false id fun h' => h h'.1

/-- The constants `1` are the ends of the conjunction chains. -/
theorem isTrue_step (c : Fin prog.length) (j : Fin ((clauseAt prog c).body.length + 1))
    (w : Fin (clauseDim B k) → A) :
    RelMap (M := (drawInterp prog bit).Map A) circIsTrue ![(stepTag c j, w)] ↔
      (j : ℕ) = (clauseAt prog c).body.length := by
  change RelMap (M := (drawInterp prog bit).Map A) ncIsTrue ![(stepTag c j, w)] ↔ _
  rw [FOInterpretation.relMap_map]
  exact (realize_ite_bot _ _ _).trans (and_iff_left (Formula.realize_top.mpr trivial))

theorem not_isTrue_atom (i : B.ι) (w : Fin (clauseDim B k) → A) :
    ¬RelMap (M := (drawInterp prog bit).Map A) circIsTrue ![(atomTag i, w)] :=
  fun h => h.elim

/-- The conjunction gates are the links of the conjunction chains. -/
theorem isAnd_step (c : Fin prog.length) (j : Fin ((clauseAt prog c).body.length + 1))
    (w : Fin (clauseDim B k) → A) :
    RelMap (M := (drawInterp prog bit).Map A) circIsAnd ![(stepTag c j, w)] ↔
      (j : ℕ) < (clauseAt prog c).body.length := by
  change RelMap (M := (drawInterp prog bit).Map A) ncIsAnd ![(stepTag c j, w)] ↔ _
  rw [FOInterpretation.relMap_map]
  exact (realize_ite_bot _ _ _).trans (and_iff_left (Formula.realize_top.mpr trivial))

theorem not_isAnd_atom (i : B.ι) (w : Fin (clauseDim B k) → A) :
    ¬RelMap (M := (drawInterp prog bit).Map A) circIsAnd ![(atomTag i, w)] :=
  fun h => h.elim

/-- The disjunction gates are the atoms. -/
theorem isOr_atom (i : B.ι) (w : Fin (clauseDim B k) → A) :
    RelMap (M := (drawInterp prog bit).Map A) circIsOr ![(atomTag i, w)] := by
  change RelMap (M := (drawInterp prog bit).Map A) ncIsOr ![(atomTag i, w)]
  rw [FOInterpretation.relMap_map]
  exact Formula.realize_top.mpr trivial

theorem not_isOr_step (c : Fin prog.length) (j : Fin ((clauseAt prog c).body.length + 1))
    (w : Fin (clauseDim B k) → A) :
    ¬RelMap (M := (drawInterp prog bit).Map A) circIsOr ![(stepTag c j, w)] :=
  fun h => h.elim

/-- **The circuit is monotone**: it has no negation gate. -/
theorem not_isNot (p : (drawInterp prog bit).Map A) :
    ¬RelMap (M := (drawInterp prog bit).Map A) circIsNot ![p] :=
  fun h => h.elim

open Classical in
/-- The outputs are the canonically padded atoms of the relation variables
`bit τ`. -/
theorem out_atom (i : B.ι) (w : Fin (clauseDim B k) → A) :
    RelMap (M := (drawInterp prog bit).Map A) ncOut ![(atomTag i, w)] ↔
      (∃ τ, bit τ = i) ∧ Canon (B.arity i) w := by
  rw [FOInterpretation.relMap_map]
  exact (realize_ite_bot _ _ _).trans (and_congr Iff.rfl realize_canonF)

theorem not_out_step (c : Fin prog.length) (j : Fin ((clauseAt prog c).body.length + 1))
    (w : Fin (clauseDim B k) → A) :
    ¬RelMap (M := (drawInterp prog bit).Map A) ncOut ![(stepTag c j, w)] :=
  fun h => h.elim

/-- **The inputs of an atom**: the conjunction chains, read at their start, of
the rules whose head is that atom, at the valuations satisfying their
guard. -/
theorem left_atom_step (i : B.ι) (w : Fin (clauseDim B k) → A) (c : Fin prog.length)
    (j : Fin ((clauseAt prog c).body.length + 1)) (u : Fin (clauseDim B k) → A) :
    RelMap (M := (drawInterp prog bit).Map A) circLeft ![(atomTag i, w), (stepTag c j, u)] ↔
      (j : ℕ) = 0 ∧ (clauseAt prog c).guard.Realize (pref le_clauseDim u) ∧
        ∃ a ∈ (clauseAt prog c).head, a.idx = i ∧ PadTup (atomIdx a) u w := by
  change RelMap (M := (drawInterp prog bit).Map A) ncLeft ![(atomTag i, w), (stepTag c j, u)] ↔ _
  rw [FOInterpretation.relMap_map]
  exact (realize_ite_bot _ _ _).trans (and_congr Iff.rfl
    (Formula.realize_inf.trans (and_congr realize_guardF realize_headOccF)))

theorem not_left_atom_atom (i i' : B.ι) (w w' : Fin (clauseDim B k) → A) :
    ¬RelMap (M := (drawInterp prog bit).Map A) circLeft ![(atomTag i, w), (atomTag i', w')] :=
  fun h => h.elim

open Classical in
/-- **The left input of a link** of a conjunction chain: its body atom. -/
theorem left_step_atom (c : Fin prog.length) (j : Fin ((clauseAt prog c).body.length + 1))
    (u : Fin (clauseDim B k) → A) (i : B.ι) (w : Fin (clauseDim B k) → A) :
    RelMap (M := (drawInterp prog bit).Map A) circLeft ![(stepTag c j, u), (atomTag i, w)] ↔
      ∃ a, (clauseAt prog c).body[(j : ℕ)]? = some a ∧ a.idx = i ∧
        PadTup (atomIdx a) u w := by
  change RelMap (M := (drawInterp prog bit).Map A) ncLeft ![(stepTag c j, u), (atomTag i, w)] ↔ _
  rw [FOInterpretation.relMap_map]
  change (((clauseAt prog c).body[(j : ℕ)]?).elim ⊥ fun a =>
    if a.idx = i then
      atomOccF a (fun j => ((0 : Fin 2), j)) fun j => ((1 : Fin 2), j)
    else ⊥ : (L.sum Language.order).Formula (Fin 2 × Fin (clauseDim B k))).Realize _ ↔ _
  cases hb : (clauseAt prog c).body[(j : ℕ)]? with
  | none => exact iff_of_false id fun ⟨_, h, _⟩ => by simp at h
  | some a =>
    rw [Option.elim_some]
    refine (realize_ite_bot _ _ _).trans ⟨fun h => ⟨a, rfl, h.1, realize_atomOccF.mp h.2⟩, ?_⟩
    rintro ⟨a', ha', hi, hp⟩
    obtain rfl : a = a' := Option.some.inj ha'
    exact ⟨hi, realize_atomOccF.mpr hp⟩

theorem not_left_step_step (c c' : Fin prog.length)
    (j : Fin ((clauseAt prog c).body.length + 1))
    (j' : Fin ((clauseAt prog c').body.length + 1)) (u u' : Fin (clauseDim B k) → A) :
    ¬RelMap (M := (drawInterp prog bit).Map A) circLeft ![(stepTag c j, u), (stepTag c' j', u')] :=
  fun h => h.elim

/-- **The right input of a link** of a conjunction chain: the next link, at
the same valuation. -/
theorem right_step_step (c c' : Fin prog.length)
    (j : Fin ((clauseAt prog c).body.length + 1))
    (j' : Fin ((clauseAt prog c').body.length + 1)) (u u' : Fin (clauseDim B k) → A) :
    RelMap (M := (drawInterp prog bit).Map A) circRight
        ![(stepTag c j, u), (stepTag c' j', u')] ↔
      (c = c' ∧ (j' : ℕ) = j + 1) ∧ u' = u := by
  change RelMap (M := (drawInterp prog bit).Map A) ncRight
    ![(stepTag c j, u), (stepTag c' j', u')] ↔ _
  rw [FOInterpretation.relMap_map]
  exact (realize_ite_bot _ _ _).trans (and_congr Iff.rfl realize_eqTupF)

theorem not_right_atom (i : B.ι) (w : Fin (clauseDim B k) → A)
    (q : (drawInterp prog bit).Map A) :
    ¬RelMap (M := (drawInterp prog bit).Map A) circRight ![(atomTag i, w), q] := by
  obtain ⟨t, u⟩ := q
  rcases t with i' | ⟨c, j⟩ <;> exact fun h => h.elim

theorem not_right_step_atom (c : Fin prog.length)
    (j : Fin ((clauseAt prog c).body.length + 1)) (u : Fin (clauseDim B k) → A) (i : B.ι)
    (w : Fin (clauseDim B k) → A) :
    ¬RelMap (M := (drawInterp prog bit).Map A) circRight ![(stepTag c j, u), (atomTag i, w)] :=
  fun h => h.elim

open Classical in
/-- The output atoms are compared by their relation variable, then
lexicographically. -/
theorem below_bit_bit (hinj : Function.Injective bit) (τ τ' : Fin c)
    (w w' : Fin (clauseDim B k) → A) :
    RelMap (M := (drawInterp prog bit).Map A) ncBelow
        ![(atomTag (bit τ), w), (atomTag (bit τ'), w')] ↔
      τ < τ' ∨ (τ = τ' ∧ tupLeLex w w') := by
  rw [FOInterpretation.relMap_map]
  change (if ∃ σ σ', bit σ = bit τ ∧ bit σ' = bit τ' ∧ σ < σ' then ⊤
    else if bit τ = bit τ' then lexTupleLeF L (clauseDim B k) else ⊥ :
      (L.sum Language.order).Formula (Fin 2 × Fin (clauseDim B k))).Realize _ ↔ _
  have hex : (∃ σ σ', bit σ = bit τ ∧ bit σ' = bit τ' ∧ σ < σ') ↔ τ < τ' :=
    ⟨fun ⟨σ, σ', h1, h2, h3⟩ => hinj h1 ▸ hinj h2 ▸ h3, fun h => ⟨τ, τ', rfl, rfl, h⟩⟩
  by_cases hlt : τ < τ'
  · rw [ite_eq_left (hex.mpr hlt)]
    exact iff_of_true (Formula.realize_top.mpr trivial) (Or.inl hlt)
  · rw [ite_eq_right (fun h => hlt (hex.mp h))]
    refine (realize_ite_bot _ _ _).trans ⟨fun h => Or.inr ⟨hinj h.1, realize_lexTupleLeF.mp h.2⟩,
      fun h => h.elim (fun h' => absurd h' hlt)
        fun h' => ⟨congrArg bit h'.1, realize_lexTupleLeF.mpr h'.2⟩⟩

end Read

end CircNum

end DescriptiveComplexity
