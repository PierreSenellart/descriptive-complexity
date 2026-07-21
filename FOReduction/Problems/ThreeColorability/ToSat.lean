/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import FOReduction.Problems.Sat
import FOReduction.Problems.ThreeColorability.Defs

/-!
# 3-colorability FO-reduces to SAT

This file constructs a (quantifier-free) first-order reduction from graph
3-colorability to CNF satisfiability, `FirstOrder.threeCol_fo_reduction_sat :
FOReduction ThreeCol SAT`, formalizing the classical encoding used by SAT
solvers:

* for every vertex `u` and color `i < 3`, a propositional variable `xᵤᵢ`
  ("`u` gets color `i`"), represented by the element `(varC i, ![u, u])`;
* for every vertex `u`, a clause `xᵤ₀ ∨ xᵤ₁ ∨ xᵤ₂`, represented by
  `(vtxClause, ![u, u])`;
* for every edge `(u, v)` and color `i`, a clause `¬xᵤᵢ ∨ ¬xᵥᵢ`, represented
  by `(edgClause i, ![u, v])`.

The resulting CNF is satisfiable iff the graph is 3-colorable
(`FirstOrder.threeColorable_iff_satisfiable`); note that the usual
"at most one color per vertex" clauses are not needed for the equivalence. All
defining formulas are quantifier-free (`FirstOrder.threeColToSat_isQuantifierFree`),
so this is even a quantifier-free reduction, the weakest reduction notion in
common use in descriptive complexity.

Elements of the interpreted universe not of the shapes above ("junk", e.g.
`(varC i, ![u, v])` with `u ≠ v`, or `(edgClause i, ![u, v])` with `(u, v)` not
an edge) are neither clauses nor occur in any clause, so they do not affect
satisfiability.
-/

namespace FirstOrder

open Language Structure BoundedFormula

/-- Tags for the tagged 2-dimensional interpretation of SAT instances in
graphs. -/
inductive ColTag : Type
  /-- `(varC i, ![u, u])` is the propositional variable "`u` gets color `i`". -/
  | varC : Fin 3 → ColTag
  /-- `(vtxClause, ![u, u])` is the clause "`u` gets some color". -/
  | vtxClause : ColTag
  /-- `(edgClause i, ![u, v])` is the clause "`u` and `v` do not both get color
  `i`" (present when `(u, v)` is an edge). -/
  | edgClause : Fin 3 → ColTag
  deriving DecidableEq, Fintype

/-- Defining formula for `satIsClause`: vertex clauses are the diagonal
`vtxClause`-elements, edge clauses for color `i` are the `edgClause i`-elements
carrying an edge. -/
def isClauseFormula : ColTag → Language.graph.Formula (Fin 1 × Fin 2)
  | .varC _ => ⊥
  | .vtxClause => Term.equal (Term.var (0, 0)) (Term.var (0, 1))
  | .edgClause _ => adj.formula₂ (Term.var (0, 0)) (Term.var (0, 1))

/-- Defining formula for `satPosIn`: the vertex clause of `u` contains
positively exactly the variables `xᵤᵢ`. -/
def posInFormula : ColTag → ColTag → Language.graph.Formula (Fin 2 × Fin 2)
  | .vtxClause, .varC _ =>
      (Term.equal (Term.var (0, 0)) (Term.var (0, 1)) ⊓
        Term.equal (Term.var (1, 0)) (Term.var (1, 1))) ⊓
      Term.equal (Term.var (0, 0)) (Term.var (1, 0))
  | _, _ => ⊥

/-- Defining formula for `satNegIn`: the edge clause of `(u, v)` for color `i`
contains negatively exactly the variables `xᵤᵢ` and `xᵥᵢ`. -/
def negInFormula : ColTag → ColTag → Language.graph.Formula (Fin 2 × Fin 2)
  | .edgClause i, .varC j =>
      if i = j then
        (adj.formula₂ (Term.var (0, 0)) (Term.var (0, 1)) ⊓
          Term.equal (Term.var (1, 0)) (Term.var (1, 1))) ⊓
        (Term.equal (Term.var (1, 0)) (Term.var (0, 0)) ⊔
          Term.equal (Term.var (1, 0)) (Term.var (0, 1)))
      else ⊥
  | _, _ => ⊥

/-- The first-order interpretation producing, from a graph, the CNF instance
expressing its 3-colorability. -/
def threeColToSat : FOInterpretation Language.graph Language.sat ColTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun t => isClauseFormula (t 0)
    | _, .posIn => fun t => posInFormula (t 0) (t 1)
    | _, .negIn => fun t => negInFormula (t 0) (t 1)

section Characterizations

variable {V : Type} [Language.graph.Structure V]

@[simp]
theorem isClause_varC (i : Fin 3) (w : Fin 2 → V) :
    ¬RelMap (M := threeColToSat.Map V) satIsClause ![(ColTag.varC i, w)] := by
  rw [FOInterpretation.relMap_map]
  simp [threeColToSat, isClauseFormula]

@[simp]
theorem isClause_vtxClause (w : Fin 2 → V) :
    RelMap (M := threeColToSat.Map V) satIsClause ![(ColTag.vtxClause, w)] ↔ w 0 = w 1 := by
  rw [FOInterpretation.relMap_map]
  simp [threeColToSat, isClauseFormula]

@[simp]
theorem isClause_edgClause (i : Fin 3) (w : Fin 2 → V) :
    RelMap (M := threeColToSat.Map V) satIsClause ![(ColTag.edgClause i, w)] ↔
      RelMap adj ![w 0, w 1] := by
  rw [FOInterpretation.relMap_map]
  simp [threeColToSat, isClauseFormula]

@[simp]
theorem posIn_iff (tc tx : ColTag) (wc wx : Fin 2 → V) :
    RelMap (M := threeColToSat.Map V) satPosIn ![(tc, wc), (tx, wx)] ↔
      (∃ i, tc = ColTag.vtxClause ∧ tx = ColTag.varC i) ∧
        (wc 0 = wc 1 ∧ wx 0 = wx 1) ∧ wc 0 = wx 0 := by
  rw [FOInterpretation.relMap_map]
  cases tc <;> cases tx <;> simp [threeColToSat, posInFormula]

@[simp]
theorem negIn_iff (tc tx : ColTag) (wc wx : Fin 2 → V) :
    RelMap (M := threeColToSat.Map V) satNegIn ![(tc, wc), (tx, wx)] ↔
      (∃ i, tc = ColTag.edgClause i ∧ tx = ColTag.varC i) ∧
        (RelMap adj ![wc 0, wc 1] ∧ wx 0 = wx 1) ∧
        (wx 0 = wc 0 ∨ wx 0 = wc 1) := by
  rw [FOInterpretation.relMap_map]
  cases tc with
  | varC i => cases tx <;> simp [threeColToSat, negInFormula]
  | vtxClause => cases tx <;> simp [threeColToSat, negInFormula]
  | edgClause i =>
    cases tx with
    | varC j =>
      rcases eq_or_ne i j with rfl | hij
      · simp [threeColToSat, negInFormula]
      · simp [threeColToSat, negInFormula, hij, Ne.symm hij]
    | vtxClause => simp [threeColToSat, negInFormula]
    | edgClause j => simp [threeColToSat, negInFormula]

end Characterizations

/-- The truth assignment induced by a coloring: `xᵤᵢ` is true iff `u` gets
color `i`. (Junk elements are assigned `False`.) -/
def colAssignment {V : Type} (col : V → Fin 3) : ColTag × (Fin 2 → V) → Prop
  | (ColTag.varC i, w) => col (w 0) = i
  | (ColTag.vtxClause, _) => False
  | (ColTag.edgClause _, _) => False

@[simp]
theorem colAssignment_varC {V : Type} (col : V → Fin 3) (i : Fin 3) (w : Fin 2 → V) :
    colAssignment col (ColTag.varC i, w) ↔ col (w 0) = i :=
  Iff.rfl

/-- Correctness of the reduction: a graph is 3-colorable iff the interpreted
CNF instance is satisfiable. -/
theorem threeColorable_iff_satisfiable (V : Type) [Language.graph.Structure V] :
    ThreeColorable V ↔ Satisfiable (threeColToSat.Map V) := by
  unfold ThreeColorable Satisfiable
  constructor
  · -- from a proper coloring to a satisfying assignment
    rintro ⟨col, hcol⟩
    refine ⟨colAssignment col, ?_⟩
    rintro ⟨tc, w⟩ hc
    match tc with
    | ColTag.varC i => exact absurd hc (isClause_varC i w)
    | ColTag.vtxClause =>
      -- the vertex clause of `w 0`: its literal `x_{w 0, col (w 0)}` is true
      rw [isClause_vtxClause] at hc
      refine ⟨(ColTag.varC (col (w 0)), ![w 0, w 0]), Or.inl ⟨?_, ?_⟩⟩
      · rw [posIn_iff]
        exact ⟨⟨_, rfl, rfl⟩, ⟨hc, by simp⟩, by simp⟩
      · simp
    | ColTag.edgClause i =>
      -- the edge clause of `(w 0, w 1)` for color `i`: since the coloring is
      -- proper, one endpoint does not get color `i`
      rw [isClause_edgClause] at hc
      have hne := hcol (w 0) (w 1) hc
      by_cases h0 : col (w 0) = i
      · refine ⟨(ColTag.varC i, ![w 1, w 1]), Or.inr ⟨?_, ?_⟩⟩
        · rw [negIn_iff]
          exact ⟨⟨i, rfl, rfl⟩, ⟨hc, by simp⟩, Or.inr (by simp)⟩
        · simp only [colAssignment_varC, Matrix.cons_val_zero]
          exact fun h1 => hne (h0.trans h1.symm)
      · refine ⟨(ColTag.varC i, ![w 0, w 0]), Or.inr ⟨?_, ?_⟩⟩
        · rw [negIn_iff]
          exact ⟨⟨i, rfl, rfl⟩, ⟨hc, by simp⟩, Or.inl (by simp)⟩
        · simpa using h0
  · -- from a satisfying assignment to a proper coloring
    rintro ⟨ν, hν⟩
    -- every vertex has at least one true color variable, by its vertex clause
    have key : ∀ u : V, ∃ i : Fin 3, ν (ColTag.varC i, ![u, u]) := by
      intro u
      obtain ⟨⟨tx, wx⟩, hx⟩ := hν (ColTag.vtxClause, ![u, u]) (by simp)
      rcases hx with ⟨hpos, hνx⟩ | ⟨hneg, -⟩
      · rw [posIn_iff] at hpos
        obtain ⟨⟨i, -, rfl⟩, ⟨-, hdiag⟩, h00⟩ := hpos
        simp only [Matrix.cons_val_zero] at h00
        have hwx : wx = ![u, u] := by
          funext j
          fin_cases j <;> simp [← h00, ← hdiag]
        exact ⟨i, hwx ▸ hνx⟩
      · rw [negIn_iff] at hneg
        simp at hneg
    choose col hcolSpec using key
    refine ⟨col, fun x y hadj heq => ?_⟩
    -- the edge clause of `(x, y)` for the common color is violated
    obtain ⟨⟨tz, wz⟩, hz⟩ := hν (ColTag.edgClause (col x), ![x, y]) (by simpa)
    rcases hz with ⟨hpos, -⟩ | ⟨hneg, hνz⟩
    · rw [posIn_iff] at hpos
      simp at hpos
    · rw [negIn_iff] at hneg
      obtain ⟨⟨i, hedg, rfl⟩, ⟨-, hdiag⟩, hor⟩ := hneg
      obtain rfl : col x = i := by simpa using hedg
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hor
      apply hνz
      rcases hor with h | h
      · have hwz : wz = ![x, x] := by
          funext j
          fin_cases j <;> simp [h, ← hdiag]
        rw [hwz]
        exact hcolSpec x
      · have hwz : wz = ![y, y] := by
          funext j
          fin_cases j <;> simp [h, ← hdiag]
        rw [hwz, heq]
        exact hcolSpec y

/-- **3-colorability FO-reduces to SAT.** The `fo_reduction` theorem: the
first-order interpretation `threeColToSat` maps a graph to a satisfiable CNF
instance iff the graph is 3-colorable. -/
def threeCol_fo_reduction_sat : ThreeCol ≤ᶠᵒ SAT where
  Tag := ColTag
  dim := 2
  toInterpretation := threeColToSat
  correct A _ := threeColorable_iff_satisfiable A

/-- The reduction is even quantifier-free. -/
theorem threeColToSat_isQuantifierFree : threeColToSat.IsQuantifierFree := by
  intro n R t
  cases R with
  | isClause =>
    change (isClauseFormula (t 0)).IsQF
    cases t 0 with
    | varC i => exact isQF_bot
    | vtxClause => exact (IsAtomic.equal _ _).isQF
    | edgClause i => exact (IsAtomic.rel _ _).isQF
  | posIn =>
    change (posInFormula (t 0) (t 1)).IsQF
    cases t 0 <;> cases t 1 <;>
      first
        | exact isQF_bot
        | exact (((IsAtomic.equal _ _).isQF.inf (IsAtomic.equal _ _).isQF).inf
            (IsAtomic.equal _ _).isQF)
  | negIn =>
    change (negInFormula (t 0) (t 1)).IsQF
    cases t 0 <;> cases t 1 <;> try exact isQF_bot
    simp only [negInFormula]
    split
    · exact (((IsAtomic.rel _ _).isQF.inf (IsAtomic.equal _ _).isQF).inf
        ((IsAtomic.equal _ _).isQF.sup (IsAtomic.equal _ _).isQF))
    · exact isQF_bot

/-- Corollary in terms of Mathlib's `SimpleGraph`: a simple graph is
3-colorable iff the CNF instance interpreted in it is satisfiable. -/
theorem SimpleGraph.colorable_iff_satisfiable {V : Type} (G : SimpleGraph V) :
    haveI := G.structure
    G.Colorable 3 ↔ Satisfiable (threeColToSat.Map V) := by
  letI := G.structure
  rw [← threeColorable_iff_colorable G,
    threeColorable_iff_satisfiable V]

end FirstOrder
