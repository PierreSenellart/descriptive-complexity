/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Counting.Restrict
import DescriptiveComplexity.Problems.TwoSat.Defs
import DescriptiveComplexity.Problems.HornSat.Defs
import DescriptiveComplexity.Problems.CliqueFamily.CountingAll

/-!
# #2SAT, #HORN-SAT, #Monotone-2SAT, and all the vertex covers of a graph

The model counts of the CNF formulas of a restricted shape:
`DescriptiveComplexity.SharpTwoSAT` (at most two literals per clause),
`DescriptiveComplexity.SharpHornSAT` (at most one positive literal per clause)
and `DescriptiveComplexity.SharpMonotoneTwoSAT` (at most two literals per
clause, all positive), each #SAT restricted to a first-order definable class
of formulas (`DescriptiveComplexity.CountingProblem.restrict`), and
`DescriptiveComplexity.SharpAllVertexCovers`, the number of vertex covers of a
graph. Deciding the first three is in PTIME; counting their models is one-call
`#P`-complete ([Valiant 1979][valiant1979complexity]).

The vertex covers of a graph are the complements of its independent sets, so
the last problem is counting all the independent sets under another name
(`DescriptiveComplexity.sharpAllVertexCovers_eq`). The three others are
reached from it by one reduction with a sign (`DescriptiveComplexity.edgeInterp`):
one clause per edge, holding its two ends as literals of that sign. With the
negative sign the models are the independent sets, the formula is a 2-CNF
and a Horn formula; with the positive sign the models are the vertex covers,
the formula a monotone 2-CNF. In both cases the models are sets of
*non-isolated* vertices, the variables of the formula, and each isolated
vertex doubles the count of the graph: the post-processing multiplies by `2`
to the number of isolated vertices.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

/-! ### The classes of formulas -/

section Sentences

variable {α : Type}

/-- The literal `(x, s)` occurs in the clause `c`, over the vocabulary of CNF
formulas. -/
noncomputable def occS (s : Bool) (c x : α) : Language.sat.Formula α :=
  Relations.formula₁ satIsClause (Term.var c) ⊓
    if s then Relations.formula₂ satPosIn (Term.var c) (Term.var x)
    else Relations.formula₂ satNegIn (Term.var c) (Term.var x)

/-- **At most two literals per clause**: among any three occurrences of a
clause, two coincide. -/
noncomputable def widthTwoS : Language.sat.Sentence :=
  Formula.iAlls (Fin 4) (Formula.iInf fun s : Fin 3 → Bool =>
    (Formula.iInf fun i : Fin 3 => occS (s i) (Sum.inr 0) (Sum.inr i.succ)) ⟹
      Formula.iSup fun p : {p : Fin 3 × Fin 3 // p.1 ≠ p.2 ∧ s p.1 = s p.2} =>
        (Term.var (Sum.inr p.1.1.succ)).equal (Term.var (Sum.inr p.1.2.succ)))

/-- **At most one positive literal per clause.** -/
noncomputable def hornS : Language.sat.Sentence :=
  fo% ∀ c x y, satIsClause(c) → satPosIn(c, x) → satPosIn(c, y) → x ≐ y

/-- **No negative literal.** -/
noncomputable def monotoneS : Language.sat.Sentence :=
  fo% ∀ c x, satIsClause(c) → ¬ satNegIn(c, x)

variable {A : Type} [Language.sat.Structure A]

theorem realize_occS {s : Bool} {c x : α} {v : α → A} :
    (occS s c x).Realize v ↔ OccIn (v c) (v x) s := by
  cases s <;> simp [occS, OccIn, IsCl, PosIn, NegIn, Formula.realize_rel₁, Formula.realize_rel₂]

theorem realize_widthTwoS : A ⊨ widthTwoS ↔ WidthAtMostTwo A := by
  simp only [widthTwoS, Sentence.Realize, Formula.realize_iAlls, Formula.realize_iInf,
    Formula.realize_imp, Formula.realize_iSup, realize_occS, Formula.realize_equal,
    Term.realize_var, Sum.elim_inr]
  constructor
  · intro h c x s hocc
    obtain ⟨⟨⟨i, j⟩, hij, hs⟩, hx⟩ := h (Fin.cons c x) s fun i => by simpa using hocc i
    exact ⟨i, j, hij, by simpa using hx, hs⟩
  · intro h w s hocc
    obtain ⟨i, j, hij, hx, hs⟩ := h (w 0) (fun i => w i.succ) s hocc
    exact ⟨⟨⟨i, j⟩, hij, hs⟩, hx⟩

theorem realize_hornS : A ⊨ hornS ↔ AtMostOnePositive A := by
  simp only [hornS, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_rel₁, Formula.realize_rel₂, Formula.realize_equal, Term.realize_var,
    Sum.elim_inr, AtMostOnePositive]
  constructor
  · intro h c x y
    exact h ![c, x, y]
  · intro h w
    exact h (w 0) (w 1) (w 2)

/-- No clause has a negative literal. -/
def NoNegative (A : Type) [Language.sat.Structure A] : Prop :=
  ∀ c x : A, RelMap satIsClause ![c] → ¬RelMap satNegIn ![c, x]

theorem realize_monotoneS : A ⊨ monotoneS ↔ NoNegative A := by
  simp only [monotoneS, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var,
    Sum.elim_inr, NoNegative]
  constructor
  · intro h c x
    exact h ![c, x]
  · intro h w
    exact h (w 0) (w 1)

end Sentences

/-! ### The problems -/

/-- **#2SAT**: the number of models of a CNF formula with at most two literals
per clause, `0` on the other formulas. -/
noncomputable def SharpTwoSAT : CountingProblem Language.sat :=
  SharpSAT.restrict widthTwoS

/-- **#HORN-SAT**: the number of models of a Horn formula, `0` on the other
formulas. -/
noncomputable def SharpHornSAT : CountingProblem Language.sat :=
  SharpSAT.restrict hornS

/-- **#Monotone-2SAT**: the number of models of a CNF formula with at most two
literals per clause, all positive, `0` on the other formulas. -/
noncomputable def SharpMonotoneTwoSAT : CountingProblem Language.sat :=
  SharpSAT.restrict (widthTwoS ⊓ monotoneS)

theorem sharpTwoSat_mem_sharpP : SharpTwoSAT ∈ SharpP :=
  SharpPDefinable.restrict sharpSat_mem_sharpP widthTwoS

theorem sharpHornSat_mem_sharpP : SharpHornSAT ∈ SharpP :=
  SharpPDefinable.restrict sharpSat_mem_sharpP hornS

theorem sharpMonotoneTwoSat_mem_sharpP : SharpMonotoneTwoSAT ∈ SharpP :=
  SharpPDefinable.restrict sharpSat_mem_sharpP _

/-! ### Graphs: independent sets and vertex covers -/

section Graph

variable {A : Type} [Language.graph.Structure A]

/-- An edge of a graph: two distinct adjacent vertices. -/
def GEdge (x y : A) : Prop :=
  x ≠ y ∧ RelMap Language.adj ![x, y]

/-- A vertex is not isolated: it is an end of an edge. -/
def NonIso (x : A) : Prop :=
  ∃ y, GEdge x y ∨ GEdge y x

/-- The condition an edge sets on a set of vertices, by sign: one end in the
set when positive, one end out of it when negative. -/
def EdgeCond (s : Bool) (S : A → Prop) : Prop :=
  ∀ x y, GEdge x y → if s then S x ∨ S y else ¬S x ∨ ¬S y

/-- A **vertex cover**: every edge has an end in it. -/
def GVertexCover (A : Type) [Language.graph.Structure A] (C : A → Prop) : Prop :=
  ∀ x y : A, x ≠ y → RelMap Language.adj ![x, y] → C x ∨ C y

theorem indepSet_iff_edgeCond (S : A → Prop) :
    IndepSet (fun x y : A => RelMap Language.adj ![x, y]) S ↔ EdgeCond false S := by
  constructor
  · intro h x y hxy
    by_contra hc
    simp only [Bool.false_eq_true, ↓reduceIte, not_or, not_not] at hc
    exact h x y hc.1 hc.2 hxy.1 hxy.2
  · intro h x y hx hy hne hadj
    have := h x y ⟨hne, hadj⟩
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    rcases this with h' | h'
    · exact h' hx
    · exact h' hy

theorem vertexCover_iff_edgeCond (C : A → Prop) : GVertexCover A C ↔ EdgeCond true C := by
  simp only [GVertexCover, EdgeCond, GEdge, ↓reduceIte]
  exact ⟨fun h x y hxy => h x y hxy.1 hxy.2, fun h x y hne hadj => h x y ⟨hne, hadj⟩⟩

/-- **The vertex covers are the complements of the independent sets.** -/
theorem card_vertexCover_eq (A : Type) [Language.graph.Structure A] :
    Nat.card {C : A → Prop // GVertexCover A C} =
      Nat.card {S : A → Prop // IndepSet (fun x y : A => RelMap Language.adj ![x, y]) S} :=
  Nat.card_congr
    { toFun := fun C => ⟨fun x => ¬C.1 x, fun x y hx hy hne hadj => (C.2 x y hne hadj).elim hx hy⟩
      invFun := fun S => ⟨fun x => ¬S.1 x, fun x y hne hadj => by
        by_contra h
        rw [not_or, not_not, not_not] at h
        exact S.2 x y h.1 h.2 hne hadj⟩
      left_inv := fun C => Subtype.ext (funext fun x => propext not_not)
      right_inv := fun S => Subtype.ext (funext fun x => propext not_not) }

/-- **Counting all the vertex covers of a graph.** -/
noncomputable def SharpAllVertexCovers : CountingProblem Language.graph where
  Count := fun A inst => Nat.card {C : A → Prop // @GVertexCover A inst C}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_vertexCover_eq A, card_vertexCover_eq B]
    exact SharpAllIndependentSets.iso_invariant e

theorem sharpAllVertexCovers_eq (A : Type) [Language.graph.Structure A] :
    SharpAllVertexCovers A = SharpAllIndependentSets A :=
  card_vertexCover_eq A

theorem sharpAllVertexCovers_mem_sharpP : SharpAllVertexCovers ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => (sharpAllVertexCovers_eq A).symm)
    sharpAllIndependentSets_mem_sharpP

/-- **Counting all the vertex covers of a graph is one-call `#P`-complete.**
Registered in the Lax archive as
[`Lax859101.AllSetsComplete.sharpAllVertexCovers_sharpP_oneCallComplete`](https://laxarchive.org/lax-859101/Lax859101.AllSetsComplete.html#s-Lax859101.AllSetsComplete.sharpAllVertexCovers_sharpP_oneCallComplete). -/
theorem sharpAllVertexCovers_sharpP_oneCallComplete :
    SharpP.OneCallComplete SharpAllVertexCovers :=
  .of_mem sharpAllVertexCovers_mem_sharpP
    ((CountingClass.oneCallHard_congr_finite fun A _ _ => (sharpAllVertexCovers_eq A).symm).mp
      sharpAllIndependentSets_sharpP_oneCallHard)

open Classical in
/-- Each isolated vertex doubles the number of sets meeting the condition. -/
theorem card_edgeCond_split [Finite A] (s : Bool) :
    Nat.card {S : A → Prop // EdgeCond s S} =
      Nat.card {S : A → Prop // (∀ x, S x → NonIso x) ∧ EdgeCond s S} *
        2 ^ Nat.card {x : A // ¬NonIso x} := by
  have hN : ∀ x y : A, GEdge x y → NonIso x ∧ NonIso y := fun x y h =>
    ⟨⟨y, Or.inl h⟩, ⟨x, Or.inr h⟩⟩
  rw [← card_subsets_eq_two_pow, ← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun S => (⟨fun x => S.1 x ∧ NonIso x, fun x h => h.2, fun x y hxy => ?_⟩,
        ⟨fun x => S.1 x ∧ ¬NonIso x, fun x h => h.2⟩)
      invFun := fun p => ⟨fun x => p.1.1 x ∨ p.2.1 x, fun x y hxy => ?_⟩
      left_inv := fun S => Subtype.ext (funext fun x => propext (by
        by_cases h : NonIso x <;> simp [h]))
      right_inv := fun p => Prod.ext (Subtype.ext (funext fun x => propext ?_))
        (Subtype.ext (funext fun x => propext ?_)) }
  · have h := S.2 x y hxy
    have hn := hN x y hxy
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> tauto
  · have h := p.1.2.2 x y hxy
    have hn := hN x y hxy
    have h1 : ¬p.2.1 x := fun h' => p.2.2 x h' hn.1
    have h2 : ¬p.2.1 y := fun h' => p.2.2 y h' hn.2
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> tauto
  · have h := p.1.2.1 x
    have h' := p.2.2 x
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact h1
      · exact absurd h2 (h' h1)
    · intro h1
      exact ⟨Or.inl h1, h h1⟩
  · have h := p.1.2.1 x
    have h' := p.2.2 x
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (h h1) h2
      · exact h1
    · intro h1
      exact ⟨Or.inr h1, h' h1⟩

/-- Among the sets of non-isolated vertices, the vertex covers are the
complements of the independent sets. -/
theorem card_edgeCond_true_eq :
    Nat.card {S : A → Prop // (∀ x, S x → NonIso x) ∧ EdgeCond true S} =
      Nat.card {S : A → Prop // (∀ x, S x → NonIso x) ∧ EdgeCond false S} := by
  have hN : ∀ x y : A, GEdge x y → NonIso x ∧ NonIso y := fun x y h =>
    ⟨⟨y, Or.inl h⟩, ⟨x, Or.inr h⟩⟩
  refine Nat.card_congr
    { toFun := fun C => ⟨fun x => NonIso x ∧ ¬C.1 x, fun x h => h.1, fun x y hxy => ?_⟩
      invFun := fun S => ⟨fun x => NonIso x ∧ ¬S.1 x, fun x h => h.1, fun x y hxy => ?_⟩
      left_inv := fun C => Subtype.ext (funext fun x => propext ⟨fun h => not_not.mp (h.2 ∘
        fun h' => ⟨h.1, h'⟩), fun h => ⟨C.2.1 x h, fun h' => h'.2 h⟩⟩)
      right_inv := fun S => Subtype.ext (funext fun x => propext ⟨fun h => not_not.mp (h.2 ∘
        fun h' => ⟨h.1, h'⟩), fun h => ⟨S.2.1 x h, fun h' => h'.2 h⟩⟩) }
  · have h := C.2.2 x y hxy
    have hn := hN x y hxy
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    tauto
  · have h := S.2.2 x y hxy
    have hn := hN x y hxy
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    tauto

end Graph

/-! ### One clause per edge -/

/-- The adjacency symbol, over the ordered expansion. -/
abbrev gAdjOSym : (Language.graph.sum Language.order).Relations 2 := Sum.inl Language.adj

/-- The domain of the clauses: the edges. -/
noncomputable def edgeDomF : (Language.graph.sum Language.order).Formula (Fin 2) :=
  ∼((Term.var 0).equal (Term.var 1)) ⊓ Relations.formula₂ gAdjOSym (Term.var 0) (Term.var 1)

/-- The variable is an end of the clause. -/
noncomputable def endF : (Language.graph.sum Language.order).Formula (Fin 2 × Fin 2) :=
  (Term.var (1, 0)).equal (Term.var (0, 0)) ⊔ (Term.var (1, 0)).equal (Term.var (0, 1))

/-- **One clause per edge, holding its two ends as literals of sign `s`**: the
tag `true` carries the clauses, on the edges, and the tag `false` the
variables, on the diagonal. -/
noncomputable def edgeInterp (s : Bool) :
    RelFOInterpretation (Language.graph.sum Language.order) Language.sat Bool 2 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun t => if t 0 then ⊤ else ⊥
    | _, .posIn => fun t => if s = true ∧ t 0 = true ∧ t 1 = false then endF else ⊥
    | _, .negIn => fun t => if s = false ∧ t 0 = true ∧ t 1 = false then endF else ⊥
  domFormula := fun t => if t then edgeDomF else (Term.var 0).equal (Term.var 1)

section Edge

variable {A : Type} [Language.graph.Structure A] [LinearOrder A] {s : Bool}

theorem realize_edgeDomF (w : Fin 2 → A) : edgeDomF.Realize w ↔ GEdge (w 0) (w 1) := by
  simp [edgeDomF, GEdge, Formula.realize_rel₂]

theorem edge_dom_true (w : Fin 2 → A) :
    ((edgeInterp s).domFormula true).Realize w ↔ GEdge (w 0) (w 1) :=
  realize_edgeDomF w

theorem edge_dom_false (w : Fin 2 → A) :
    ((edgeInterp s).domFormula false).Realize w ↔ w 0 = w 1 := by
  simp [edgeInterp]

/-- The variable of a vertex. -/
def varPt (s : Bool) (x : A) : (edgeInterp s).MapRel A :=
  ⟨(false, ![x, x]), (edge_dom_false _).mpr rfl⟩

/-- The clause of an edge. -/
def clPt (s : Bool) (x y : A) (h : GEdge x y) : (edgeInterp s).MapRel A :=
  ⟨(true, ![x, y]), (edge_dom_true _).mpr h⟩

theorem eq_varPt (p : (edgeInterp s).MapRel A) (h : p.1.1 = false) : p = varPt s (p.1.2 0) := by
  obtain ⟨⟨t, w⟩, hw⟩ := p
  change t = false at h
  subst h
  have h1 : w 0 = w 1 := (edge_dom_false w).mp hw
  refine Subtype.ext (Prod.ext rfl (funext fun i => ?_))
  fin_cases i
  · rfl
  · exact h1.symm

theorem edge_isCl (p : (edgeInterp s).MapRel A) : RelMap satIsClause ![p] ↔ p.1.1 = true := by
  rw [RelFOInterpretation.relMap_mapRel]
  obtain ⟨⟨t, w⟩, hw⟩ := p
  cases t <;> simp [edgeInterp]

theorem edge_posIn (p q : (edgeInterp s).MapRel A) :
    RelMap satPosIn ![p, q] ↔ s = true ∧ p.1.1 = true ∧ q.1.1 = false ∧
      (q.1.2 0 = p.1.2 0 ∨ q.1.2 0 = p.1.2 1) := by
  rw [RelFOInterpretation.relMap_mapRel]
  obtain ⟨⟨t, w⟩, hw⟩ := p
  obtain ⟨⟨t', w'⟩, hw'⟩ := q
  cases s <;> cases t <;> cases t' <;> simp [edgeInterp, endF]

theorem edge_negIn (p q : (edgeInterp s).MapRel A) :
    RelMap satNegIn ![p, q] ↔ s = false ∧ p.1.1 = true ∧ q.1.1 = false ∧
      (q.1.2 0 = p.1.2 0 ∨ q.1.2 0 = p.1.2 1) := by
  rw [RelFOInterpretation.relMap_mapRel]
  obtain ⟨⟨t, w⟩, hw⟩ := p
  obtain ⟨⟨t', w'⟩, hw'⟩ := q
  cases s <;> cases t <;> cases t' <;> simp [edgeInterp, endF]

theorem edge_satOccurs (p : (edgeInterp s).MapRel A) :
    SatOccurs ((edgeInterp s).MapRel A) p ↔ p.1.1 = false ∧ NonIso (p.1.2 0) := by
  constructor
  · rintro ⟨c, hc, h⟩
    have hc' := (edge_isCl c).mp hc
    have hedge : GEdge (c.1.2 0) (c.1.2 1) := (edge_dom_true _).mp (hc' ▸ c.2)
    have key : p.1.1 = false ∧ (p.1.2 0 = c.1.2 0 ∨ p.1.2 0 = c.1.2 1) := by
      rcases h with h | h
      · exact ⟨((edge_posIn c p).mp h).2.2.1, ((edge_posIn c p).mp h).2.2.2⟩
      · exact ⟨((edge_negIn c p).mp h).2.2.1, ((edge_negIn c p).mp h).2.2.2⟩
    refine ⟨key.1, ?_⟩
    rcases key.2 with h' | h'
    · exact ⟨c.1.2 1, Or.inl (h' ▸ hedge)⟩
    · exact ⟨c.1.2 0, Or.inr (h' ▸ hedge)⟩
  · rintro ⟨hf, y, hy | hy⟩
    · refine ⟨clPt s _ _ hy, (edge_isCl _).mpr rfl, ?_⟩
      cases s
      · exact Or.inr ((edge_negIn _ _).mpr ⟨rfl, rfl, hf, Or.inl rfl⟩)
      · exact Or.inl ((edge_posIn _ _).mpr ⟨rfl, rfl, hf, Or.inl rfl⟩)
    · refine ⟨clPt s _ _ hy, (edge_isCl _).mpr rfl, ?_⟩
      cases s
      · exact Or.inr ((edge_negIn _ _).mpr ⟨rfl, rfl, hf, Or.inr rfl⟩)
      · exact Or.inl ((edge_posIn _ _).mpr ⟨rfl, rfl, hf, Or.inr rfl⟩)

/-- **The models of the formula of the edges are the sets of non-isolated
vertices meeting the condition of the sign.** -/
noncomputable def edgeModelEquiv :
    {ν : (edgeInterp s).MapRel A → Prop // SatModel _ ν} ≃
      {S : A → Prop // (∀ x, S x → NonIso x) ∧ EdgeCond s S} where
  toFun ν := ⟨fun x => ν.1 (varPt s x), fun x hx => ((edge_satOccurs _).mp (ν.2.2 _ hx)).2,
    fun x y hxy => by
      obtain ⟨q, hq⟩ := ν.2.1 (clPt s x y hxy) ((edge_isCl _).mpr rfl)
      rcases hq with ⟨hp, hν⟩ | ⟨hn, hν⟩
      · obtain ⟨hs, -, hqf, hq0⟩ := (edge_posIn _ _).mp hp
        rw [eq_varPt q hqf] at hν
        subst hs
        simp only [↓reduceIte]
        rcases hq0 with h | h
        · have h' : q.1.2 0 = x := h
          rw [h'] at hν
          exact Or.inl hν
        · have h' : q.1.2 0 = y := h
          rw [h'] at hν
          exact Or.inr hν
      · obtain ⟨hs, -, hqf, hq0⟩ := (edge_negIn _ _).mp hn
        rw [eq_varPt q hqf] at hν
        subst hs
        simp only [Bool.false_eq_true, ↓reduceIte]
        rcases hq0 with h | h
        · have h' : q.1.2 0 = x := h
          rw [h'] at hν
          exact Or.inl hν
        · have h' : q.1.2 0 = y := h
          rw [h'] at hν
          exact Or.inr hν⟩
  invFun S := ⟨fun p => p.1.1 = false ∧ S.1 (p.1.2 0), fun c hc => by
      have hc' := (edge_isCl c).mp hc
      have hedge : GEdge (c.1.2 0) (c.1.2 1) := (edge_dom_true _).mp (hc' ▸ c.2)
      have h := S.2.2 _ _ hedge
      cases s
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        rcases h with h | h
        · exact ⟨varPt false (c.1.2 0), Or.inr ⟨(edge_negIn _ _).mpr ⟨rfl, hc', rfl, Or.inl rfl⟩,
            fun h' => h h'.2⟩⟩
        · exact ⟨varPt false (c.1.2 1), Or.inr ⟨(edge_negIn _ _).mpr ⟨rfl, hc', rfl, Or.inr rfl⟩,
            fun h' => h h'.2⟩⟩
      · simp only [↓reduceIte] at h
        rcases h with h | h
        · exact ⟨varPt true (c.1.2 0), Or.inl ⟨(edge_posIn _ _).mpr ⟨rfl, hc', rfl, Or.inl rfl⟩,
            rfl, h⟩⟩
        · exact ⟨varPt true (c.1.2 1), Or.inl ⟨(edge_posIn _ _).mpr ⟨rfl, hc', rfl, Or.inr rfl⟩,
            rfl, h⟩⟩,
    fun p hp => (edge_satOccurs p).mpr ⟨hp.1, S.2.1 _ hp.2⟩⟩
  left_inv ν := Subtype.ext (funext fun p => propext (by
    constructor
    · rintro ⟨hf, h⟩
      change ν.1 (varPt s (p.1.2 0)) at h
      rwa [← eq_varPt p hf] at h
    · intro h
      have hf := ((edge_satOccurs p).mp (ν.2.2 p h)).1
      exact ⟨hf, (eq_varPt p hf) ▸ h⟩))
  right_inv S := Subtype.ext (funext fun x => propext ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩)

/-- The adjacency symbol. -/
abbrev gAdjSym : Language.graph.Relations 2 := Language.adj

/-- `x` is isolated. -/
noncomputable def isoF {α : Type} (x : α) : Language.graph.Formula α :=
  fo%[x] ∀ y, ¬ ((¬ x ≐ y ∧ gAdjSym(x, y)) ∨ (¬ y ≐ x ∧ gAdjSym(y, x)))

/-- The number of isolated vertices, as a polynomial term. -/
noncomputable def isoCount : PolyTerm Language.graph :=
  .count (LHom.sumInl.onFormula (isoF (0 : Fin 1)))

omit [LinearOrder A] in
theorem eval_isoCount [LinearOrder A] : isoCount.eval A = Nat.card {x : A // ¬NonIso x} := by
  rw [isoCount, PolyTerm.eval_count_one]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
  rw [LHom.realize_onFormula, isoF]
  simp only [Formula.realize_iAlls, Formula.realize_not, Formula.realize_sup, Formula.realize_inf,
    Formula.realize_equal, Formula.realize_rel₂, Term.realize_var, Sum.elim_inl, Sum.elim_inr,
    NonIso, GEdge, not_exists]
  exact ⟨fun h y => h fun _ => y, fun h y => h (y 0)⟩

/-- The count of the graph is the model count of the formula of its edges,
doubled for each isolated vertex. -/
theorem sharpAllIndependentSets_eq_edge [Finite A] :
    SharpAllIndependentSets A = SharpSAT ((edgeInterp s).MapRel A) *
      2 ^ Nat.card {x : A // ¬NonIso x} := by
  rw [sharpAllIndependentSets_apply, sharpSat_apply, Nat.card_congr edgeModelEquiv,
    Nat.card_congr (Equiv.subtypeEquivRight indepSet_iff_edgeCond), card_edgeCond_split]
  cases s
  · rfl
  · rw [card_edgeCond_true_eq]

/-- **Counting all the independent sets reduces to #SAT with one call**, the
formula being one clause of sign `s` per edge. -/
noncomputable def sharpAllIndependentSets_oneCall_sharpSat (s : Bool) :
    SharpAllIndependentSets ≤ᶜ[≤] SharpSAT where
  Tag := Bool
  dim := 2
  toRelInterpretation := edgeInterp s
  dom_nonempty := fun A _ _ _ _ =>
    ⟨false, fun _ => Classical.arbitrary A, (edge_dom_false (s := s) _).mpr rfl⟩
  post := .mul .oracle (.pow2 isoCount)
  correct := fun A _ _ _ _ => by
    change SharpAllIndependentSets A = SharpSAT ((edgeInterp s).MapRel A) * 2 ^ isoCount.eval A
    rw [eval_isoCount, sharpAllIndependentSets_eq_edge]

/-! ### What the formula of the edges is -/

/-- Every occurrence of the formula of the edges has the sign `s`, and is an
end of its clause. -/
theorem edge_occIn {c p : (edgeInterp s).MapRel A} {t : Bool} (h : OccIn c p t) :
    t = s ∧ p = varPt s (p.1.2 0) ∧ (p.1.2 0 = c.1.2 0 ∨ p.1.2 0 = c.1.2 1) := by
  obtain ⟨-, h⟩ := h
  cases t
  · obtain ⟨hs, -, hf, h0⟩ := (edge_negIn c p).mp h
    exact ⟨hs.symm, eq_varPt p hf, h0⟩
  · obtain ⟨hs, -, hf, h0⟩ := (edge_posIn c p).mp h
    exact ⟨hs.symm, eq_varPt p hf, h0⟩

theorem edge_widthAtMostTwo : WidthAtMostTwo ((edgeInterp s).MapRel A) := by
  intro c x t hocc
  have h := fun i => edge_occIn (hocc i)
  have hx : ∀ i, x i = varPt s ((x i).1.2 0) := fun i => (h i).2.1
  have hst : ∀ i j, t i = t j := fun i j => (h i).1.trans (h j).1.symm
  have hv : ∀ i j, (x i).1.2 0 = (x j).1.2 0 → x i = x j := fun i j he => by
    rw [hx i, hx j, he]
  rcases (h 0).2.2 with h0 | h0 <;> rcases (h 1).2.2 with h1 | h1 <;>
    rcases (h 2).2.2 with h2 | h2
  all_goals first
    | exact ⟨0, 1, by decide, hv 0 1 (h0.trans h1.symm), hst 0 1⟩
    | exact ⟨0, 2, by decide, hv 0 2 (h0.trans h2.symm), hst 0 2⟩
    | exact ⟨1, 2, by decide, hv 1 2 (h1.trans h2.symm), hst 1 2⟩

theorem edge_atMostOnePositive : AtMostOnePositive ((edgeInterp false).MapRel A) :=
  fun _ _ _ _ h => absurd ((edge_posIn _ _).mp h).1 Bool.false_ne_true

theorem edge_noNegative : NoNegative ((edgeInterp true).MapRel A) :=
  fun _ _ _ h => Bool.noConfusion ((edge_negIn _ _).mp h).1

end Edge

/-! ### Completeness -/

/-- **#2SAT is one-call `#P`-complete.**
Registered in the Lax archive as
[`Lax859101.RestrictedSatComplete.sharpTwoSat_sharpP_oneCallComplete`](https://laxarchive.org/lax-859101/Lax859101.RestrictedSatComplete.html#s-Lax859101.RestrictedSatComplete.sharpTwoSat_sharpP_oneCallComplete). -/
theorem sharpTwoSat_sharpP_oneCallComplete : SharpP.OneCallComplete SharpTwoSAT :=
  .of_mem sharpTwoSat_mem_sharpP (CountingClass.OneCallHard.of_oneCall
    ((sharpAllIndependentSets_oneCall_sharpSat false).restrict widthTwoS fun _ _ _ _ _ =>
      realize_widthTwoS.mpr edge_widthAtMostTwo)
    sharpAllIndependentSets_sharpP_oneCallHard)

/-- **#HORN-SAT is one-call `#P`-complete.**
Registered in the Lax archive as
[`Lax859101.RestrictedSatComplete.sharpHornSat_sharpP_oneCallComplete`](https://laxarchive.org/lax-859101/Lax859101.RestrictedSatComplete.html#s-Lax859101.RestrictedSatComplete.sharpHornSat_sharpP_oneCallComplete). -/
theorem sharpHornSat_sharpP_oneCallComplete : SharpP.OneCallComplete SharpHornSAT :=
  .of_mem sharpHornSat_mem_sharpP (CountingClass.OneCallHard.of_oneCall
    ((sharpAllIndependentSets_oneCall_sharpSat false).restrict hornS fun _ _ _ _ _ =>
      realize_hornS.mpr edge_atMostOnePositive)
    sharpAllIndependentSets_sharpP_oneCallHard)

/-- **#Monotone-2SAT is one-call `#P`-complete.**
Registered in the Lax archive as
[`Lax859101.RestrictedSatComplete.sharpMonotoneTwoSat_sharpP_oneCallComplete`](https://laxarchive.org/lax-859101/Lax859101.RestrictedSatComplete.html#s-Lax859101.RestrictedSatComplete.sharpMonotoneTwoSat_sharpP_oneCallComplete). -/
theorem sharpMonotoneTwoSat_sharpP_oneCallComplete : SharpP.OneCallComplete SharpMonotoneTwoSAT :=
  .of_mem sharpMonotoneTwoSat_mem_sharpP (CountingClass.OneCallHard.of_oneCall
    ((sharpAllIndependentSets_oneCall_sharpSat true).restrict _ fun _ _ _ _ _ =>
      Formula.realize_inf.mpr ⟨realize_widthTwoS.mpr edge_widthAtMostTwo,
        realize_monotoneS.mpr edge_noNegative⟩)
    sharpAllIndependentSets_sharpP_oneCallHard)

end DescriptiveComplexity
