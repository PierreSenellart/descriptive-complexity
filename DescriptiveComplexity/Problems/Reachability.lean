/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.HornSat.Hardness
import DescriptiveComplexity.FixedPoint
import DescriptiveComplexity.FixedPointHorn
import DescriptiveComplexity.LogSpace
import DescriptiveComplexity.TransitiveClosure

/-!
# Reachability, and the Horn fragment at work

The problem REACH – is some marked target reachable from some marked source in
a directed graph? – and its complement UNREACH, over the vocabulary
`FirstOrder.Language.stGraph` of graphs with marked sources and targets.

The point of this file is UNREACH: it is the worked instance of the SO-Horn
fragment of `DescriptiveComplexity.SecondOrderHorn`. Its Horn program guesses a binary
relation `T` and forces it, by two rules, to contain the transitive closure of
the edge relation, then rules out with a goal clause the case of a marked
target lying in `T` (or being itself a marked source):

```
             edge(x, y) → T(x, y)
  T(x, y) ∧  edge(y, z) → T(x, z)
  T(x, y) ∧ source(x) ∧ target(y) → ⊥
            source(x) ∧ target(x) → ⊥
```

Such a program is satisfiable exactly when its *least* model – here the
transitive closure – already satisfies the goal clauses, which is why the
existential second-order quantifier in front of a Horn kernel expresses a
polynomial-time property rather than a nondeterministic guess. That is the
content of `DescriptiveComplexity.unreach_sigmaSOHornDefinable`, and with the Horn
discharge it gives `DescriptiveComplexity.unreach_le_hornSat`: UNREACH first-order
reduces to HORN-SAT.

Note that it is the *complement* that the fragment defines: goal clauses can
only rule models out. This is the usual state of affairs for SO-Horn, and
harmless, both problems being in polynomial time.

The same file also places UNREACH one level lower, in
`DescriptiveComplexity.NL`: the Krom fragment defines it by a *two-literal*
program guessing the set `U` of vertices from which a marked target is
reachable,

```
              target(x) → U(x)
  edge(x, y)            → ¬U(y) ∨ U(x)
              source(x) → ¬U(x)
```

and the same asymmetry appears one level down, for the same reason. A clausal
fragment states closure and rejection, so it defines UNREACH head-on
(`DescriptiveComplexity.unreach_mem_NL`) while REACH would need the guessed set to be
*contained* in the true reachable set – a minimality condition no clause can
impose. At the Horn level the way out was the equivalence with FO(LFP), a full
logic closed under negation; at the Krom level the corresponding statement is
`NL = coNL`, i.e. Immerman–Szelepcsényi, which this library does not (yet)
prove. So `REACH ∈ NL` is exactly one Immerman–Szelepcsényi away from
`DescriptiveComplexity.unreach_mem_NL`; see `ROADMAP.md` §4.
-/

/- The vocabulary of graphs with marked sources and targets lives in Mathlib's
`FirstOrder.Language` namespace, next to `Language.graph` – a project-local
`Language` namespace would shadow Mathlib's under `open Language`. -/
namespace FirstOrder

namespace Language

/-- Relation symbols of the vocabulary of graphs with marked sources and
targets. -/
inductive stGraphRel : ℕ → Type
  /-- `edge a b`: there is an edge from `a` to `b`. -/
  | edge : stGraphRel 2
  /-- `source a`: the vertex `a` is a marked source. -/
  | source : stGraphRel 1
  /-- `target a`: the vertex `a` is a marked target. -/
  | target : stGraphRel 1
  deriving DecidableEq

/-- The relational vocabulary of directed graphs with marked sources and
targets. -/
protected def stGraph : Language :=
  ⟨fun _ => Empty, stGraphRel⟩
  deriving IsRelational

/-- The edge symbol. -/
abbrev sgEdge : Language.stGraph.Relations 2 := .edge

/-- The marked-source symbol. -/
abbrev sgSource : Language.stGraph.Relations 1 := .source

/-- The marked-target symbol. -/
abbrev sgTarget : Language.stGraph.Relations 1 := .target

/-- The edge symbol in the ordered expansion. -/
abbrev sgEdgeO : (Language.stGraph.sum Language.order).Relations 2 := Sum.inl sgEdge

/-- The marked-source symbol in the ordered expansion. -/
abbrev sgSourceO : (Language.stGraph.sum Language.order).Relations 1 := Sum.inl sgSource

/-- The marked-target symbol in the ordered expansion. -/
abbrev sgTargetO : (Language.stGraph.sum Language.order).Relations 1 := Sum.inl sgTarget

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The problem -/

section Defs

variable {A : Type} [Language.stGraph.Structure A]

/-- The edge relation of a marked graph. -/
def SGEdge (a b : A) : Prop := RelMap sgEdge ![a, b]

/-- Being a marked source. -/
def SGSource (a : A) : Prop := RelMap sgSource ![a]

/-- Being a marked target. -/
def SGTarget (a : A) : Prop := RelMap sgTarget ![a]

variable (A) in
/-- Some marked target is reachable from some marked source, along a
(possibly empty) directed path. -/
def Reachable : Prop :=
  ∃ s t : A, SGSource s ∧ SGTarget t ∧ Relation.ReflTransGen SGEdge s t

end Defs

section Iso

variable {A B : Type} [Language.stGraph.Structure A] [Language.stGraph.Structure B]

private theorem sgEdge_map (e : A ≃[Language.stGraph] B) (a b : A) :
    SGEdge a b ↔ SGEdge (e a) (e b) :=
  relMap_equiv₂ e sgEdge a b

private theorem reflTransGen_map (e : A ≃[Language.stGraph] B) {a b : A}
    (h : Relation.ReflTransGen SGEdge a b) :
    Relation.ReflTransGen SGEdge (e a) (e b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ((sgEdge_map e _ _).mp hbc)

private theorem reachable_of_iso (e : A ≃[Language.stGraph] B) (h : Reachable A) :
    Reachable B := by
  obtain ⟨s, t, hs, ht, hpath⟩ := h
  exact ⟨e s, e t, (relMap_equiv₁ e sgSource s).mp hs,
    (relMap_equiv₁ e sgTarget t).mp ht, reflTransGen_map e hpath⟩

/-- Reachability is isomorphism-invariant. -/
theorem reachable_iso (e : A ≃[Language.stGraph] B) : Reachable A ↔ Reachable B :=
  ⟨reachable_of_iso e, reachable_of_iso e.symm⟩

end Iso

/-- REACH, as a problem on graphs with marked sources and targets. -/
def REACH : DecisionProblem Language.stGraph where
  Holds := fun A inst => @Reachable A inst
  iso_invariant := fun e => reachable_iso e

/-- UNREACH, the complement of REACH: no marked target is reachable from a
marked source. -/
def UNREACH : DecisionProblem Language.stGraph := REACHᶜ

/-! ### The Horn program -/

/-- The block of the SO-Horn definition of UNREACH: one binary relation
variable, forced to contain the transitive closure of the edge relation. -/
def reachBlock : SOBlock where
  ι := Unit
  arity := fun _ => 2

/-- The atom `T (xᵢ, xⱼ)` of the guessed relation. -/
def tAtom (i j : Fin 3) : SOAtom reachBlock 3 :=
  ⟨(), ![i, j]⟩

/-- The guard `edge (xᵢ, xⱼ)`. Guards live over the ordered expansion of the
vocabulary, as `DescriptiveComplexity.SigmaSOHornDefinable` requires; this program
happens not to need the order. -/
noncomputable def edgeG (i j : Fin 3) :
    (Language.stGraph.sum Language.order).Formula (Fin 3) :=
  Relations.formula₂ sgEdgeO (Term.var i) (Term.var j)

/-- The guard `source xᵢ`. -/
noncomputable def sourceG (i : Fin 3) :
    (Language.stGraph.sum Language.order).Formula (Fin 3) :=
  Relations.formula₁ sgSourceO (Term.var i)

/-- The guard `target xᵢ`. -/
noncomputable def targetG (i : Fin 3) :
    (Language.stGraph.sum Language.order).Formula (Fin 3) :=
  Relations.formula₁ sgTargetO (Term.var i)

/-- Base rule: an edge is in `T`. -/
noncomputable def reachC1 :
    HornClause (Language.stGraph.sum Language.order) reachBlock 3 :=
  { guard := edgeG 0 1, body := [], head := some (tAtom 0 1) }

/-- Inductive rule: `T` is closed under appending an edge. -/
noncomputable def reachC2 :
    HornClause (Language.stGraph.sum Language.order) reachBlock 3 :=
  { guard := edgeG 1 2, body := [tAtom 0 1], head := some (tAtom 0 2) }

/-- Goal clause: no marked target is in `T` from a marked source. -/
noncomputable def reachC3 :
    HornClause (Language.stGraph.sum Language.order) reachBlock 3 :=
  { guard := sourceG 0 ⊓ targetG 1, body := [tAtom 0 1], head := none }

/-- Goal clause: no vertex is both a marked source and a marked target (the
empty path). -/
noncomputable def reachC4 :
    HornClause (Language.stGraph.sum Language.order) reachBlock 3 :=
  { guard := sourceG 0 ⊓ targetG 0, body := [], head := none }

/-- The Horn program defining UNREACH: two rules generating the transitive
closure of the edge relation into `T`, and two goal clauses forbidding a marked
target to be reached from a marked source. -/
noncomputable def reachProgram :
    HornProgram (Language.stGraph.sum Language.order) reachBlock 3 :=
  [reachC1, reachC2, reachC3, reachC4]

/-! ### Correctness of the program -/

section Program

variable {A : Type} [Language.stGraph.Structure A] [LinearOrder A]

/-- The relation guessed by an assignment of the block. -/
def TRel (ρ : reachBlock.Assignment A) (x y : A) : Prop := ρ () ![x, y]

omit [Language.stGraph.Structure A] [LinearOrder A] in
private theorem tAtom_holds (ρ : reachBlock.Assignment A) (v : Fin 3 → A) (i j : Fin 3) :
    (tAtom i j).Holds ρ v ↔ TRel ρ (v i) (v j) := by
  refine iff_of_eq (congrArg (ρ ()) (funext fun l => ?_))
  fin_cases l <;> rfl

private theorem realize_edgeG (v : Fin 3 → A) (i j : Fin 3) :
    (edgeG i j).Realize v ↔ SGEdge (v i) (v j) := by
  rw [edgeG, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

private theorem realize_sourceG (v : Fin 3 → A) (i : Fin 3) :
    (sourceG i).Realize v ↔ SGSource (v i) := by
  rw [sourceG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

private theorem realize_targetG (v : Fin 3 → A) (i : Fin 3) :
    (targetG i).Realize v ↔ SGTarget (v i) := by
  rw [targetG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

private theorem realize_srcTgtG (v : Fin 3 → A) (i j : Fin 3) :
    (sourceG i ⊓ targetG j).Realize v ↔ SGSource (v i) ∧ SGTarget (v j) := by
  rw [Formula.realize_inf, realize_sourceG, realize_targetG]

/-- What it means for an assignment to satisfy the program: the guessed
relation contains the transitive closure of the edge relation, and meets no
source-target pair. -/
theorem reachProgram_holds_iff (ρ : reachBlock.Assignment A) :
    reachProgram.Holds ρ ↔
      ((∀ x y : A, SGEdge x y → TRel ρ x y) ∧
        (∀ x y z : A, TRel ρ x y → SGEdge y z → TRel ρ x z)) ∧
      ((∀ x y : A, TRel ρ x y → SGSource x → SGTarget y → False) ∧
        ∀ x : A, SGSource x → SGTarget x → False) := by
  constructor
  · intro h
    refine ⟨⟨fun x y hxy => ?_, fun x y z hxy hyz => ?_⟩, fun x y hxy hx hy => ?_,
      fun x hx hy => ?_⟩
    · have hcl := h ![x, y, x] reachC1 (by simp [reachProgram])
      exact (tAtom_holds ρ _ 0 1).mp
        (hcl ⟨(realize_edgeG _ 0 1).mpr hxy, by simp [reachC1]⟩)
    · have hcl := h ![x, y, z] reachC2 (by simp [reachProgram])
      refine (tAtom_holds ρ _ 0 2).mp (hcl ⟨(realize_edgeG _ 1 2).mpr hyz, ?_⟩)
      intro a ha
      simp only [reachC2, List.mem_singleton] at ha
      subst ha
      exact (tAtom_holds ρ _ 0 1).mpr hxy
    · have hcl := h ![x, y, x] reachC3 (by simp [reachProgram])
      refine hcl ⟨(realize_srcTgtG _ 0 1).mpr ⟨hx, hy⟩, ?_⟩
      intro a ha
      simp only [reachC3, List.mem_singleton] at ha
      subst ha
      exact (tAtom_holds ρ _ 0 1).mpr hxy
    · have hcl := h ![x, x, x] reachC4 (by simp [reachProgram])
      exact hcl ⟨(realize_srcTgtG _ 0 0).mpr ⟨hx, hy⟩, by simp [reachC4]⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩ v c hc
    simp only [reachProgram, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · rintro ⟨hg, -⟩
      exact (tAtom_holds ρ _ 0 1).mpr (h1 _ _ ((realize_edgeG _ 0 1).mp hg))
    · rintro ⟨hg, hb⟩
      refine (tAtom_holds ρ _ 0 2).mpr (h2 _ _ _ ?_ ((realize_edgeG _ 1 2).mp hg))
      exact (tAtom_holds ρ _ 0 1).mp (hb _ (by simp [reachC2]))
    · rintro ⟨hg, hb⟩
      obtain ⟨hs, ht⟩ := (realize_srcTgtG _ 0 1).mp hg
      exact h3 _ _ ((tAtom_holds ρ _ 0 1).mp (hb _ (by simp [reachC3]))) hs ht
    · rintro ⟨hg, -⟩
      obtain ⟨hs, ht⟩ := (realize_srcTgtG _ 0 0).mp hg
      exact h4 _ hs ht

/-- The transitive closure of the edge relation, as an assignment of the
block: the least model of the two rules of the program. -/
def transClosureAssign : reachBlock.Assignment A :=
  fun _ w => Relation.TransGen SGEdge (w ⟨0, Nat.zero_lt_two⟩) (w ⟨1, Nat.one_lt_two⟩)

omit [LinearOrder A] in
@[simp]
theorem tRel_transClosureAssign (x y : A) :
    TRel (transClosureAssign (A := A)) x y ↔ Relation.TransGen SGEdge x y :=
  Iff.rfl

omit [LinearOrder A] in
/-- Any model of the two rules of the program contains the transitive closure
of the edge relation. -/
theorem transGen_tRel {ρ : reachBlock.Assignment A}
    (h1 : ∀ x y : A, SGEdge x y → TRel ρ x y)
    (h2 : ∀ x y z : A, TRel ρ x y → SGEdge y z → TRel ρ x z) {a b : A}
    (h : Relation.TransGen SGEdge a b) : TRel ρ a b := by
  induction h with
  | single hab => exact h1 _ _ hab
  | tail _ hbc ih => exact h2 _ _ _ ih hbc

end Program

/-! ### UNREACH is SO-Horn definable -/

/-- **UNREACH is SO-Horn definable**: the guessed relation is forced to
contain the transitive closure of the edge relation, and the goal clauses
forbid it to link a marked source to a marked target. The witness in the
nontrivial direction *is* the transitive closure – the least model of the two
rules. -/
theorem unreach_sigmaSOHornDefinable : SigmaSOHornDefinable UNREACH := by
  refine ⟨reachBlock, 3, reachProgram, ?_⟩
  intro A _ _ _ _
  constructor
  · intro h
    refine ⟨transClosureAssign, (reachProgram_holds_iff _).mpr
      ⟨⟨fun x y hxy => Relation.TransGen.single hxy,
        fun x y z hxy hyz => Relation.TransGen.tail hxy hyz⟩, fun x y hxy hx hy => ?_,
        fun x hx hy => ?_⟩⟩
    · exact h ⟨x, y, hx, hy, hxy.to_reflTransGen⟩
    · exact h ⟨x, x, hx, hy, Relation.ReflTransGen.refl⟩
  · rintro ⟨ρ, hρ⟩ ⟨s, t, hs, ht, hpath⟩
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (reachProgram_holds_iff ρ).mp hρ
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hpath with rfl | htg
    · exact h4 _ hs ht
    · exact h3 _ _ (transGen_tRel h1 h2 htg) hs ht

/-- **UNREACH is in PTIME**, by definition of the class as SO-Horn
definability. -/
theorem unreach_mem_PTIME : UNREACH ∈ PTIME :=
  unreach_sigmaSOHornDefinable

/-- **UNREACH first-order reduces to HORN-SAT**, by the Horn discharge. -/
theorem unreach_le_hornSat : Nonempty (UNREACH ≤ᶠᵒ[≤] HORNSAT) :=
  hornSat_hard_of_sigmaSOHornDefinable UNREACH unreach_sigmaSOHornDefinable

/-- UNREACH is FO(LFP) definable, being SO-Horn definable. -/
theorem unreach_lfpDefinable : LFPDefinable UNREACH :=
  unreach_sigmaSOHornDefinable.lfpDefinable

/-- **REACH is FO(LFP) definable** – and this is a statement the Horn fragment
cannot make head-on. Reachability is the complement of the SO-Horn definable
UNREACH, and complementing is free in the logic
(`DescriptiveComplexity.LFPDefinable.compl`), while a goal clause can only reject. -/
theorem reach_lfpDefinable : LFPDefinable REACH :=
  SigmaSOHornDefinable.compl_lfpDefinable unreach_sigmaSOHornDefinable

/-- **REACH is in PTIME** after all: what the fragment cannot say head-on it
can say through the equivalence with FO(LFP)
(`DescriptiveComplexity.SigmaSOHornDefinable.compl`). -/
theorem reach_mem_PTIME : REACH ∈ PTIME := by
  have h := unreach_sigmaSOHornDefinable.compl
  rwa [UNREACH, DecisionProblem.compl_compl] at h

/-! ### UNREACH is SO-Krom definable, hence in NL

The Krom fragment needs no transitive closure: it guesses the set of vertices
from which a marked target is reachable, closes it under *predecessors* – a
two-literal implication – and forbids a marked source to belong to it. -/

/-- The block of the SO-Krom definition of UNREACH: one unary relation
variable, the set of vertices from which a marked target is reachable. -/
def uBlock : SOBlock where
  ι := Unit
  arity := fun _ => 1

/-- The atom `U xᵢ` of the guessed set. -/
def uAtom (i : Fin 3) : SOAtom uBlock 3 :=
  ⟨(), ![i]⟩

/-- The literal `U xᵢ`, positive or negated. -/
def uLit (i : Fin 3) (pos : Bool) : KromLit uBlock 3 :=
  ⟨uAtom i, pos⟩

/-- A marked target belongs to `U`. -/
noncomputable def unreachK1 :
    KromClause (Language.stGraph.sum Language.order) uBlock 3 :=
  { guard := targetG 0, lit₁ := some (uLit 0 true), lit₂ := none }

/-- `U` is closed under predecessors: an edge into `U` starts in `U`. -/
noncomputable def unreachK2 :
    KromClause (Language.stGraph.sum Language.order) uBlock 3 :=
  { guard := edgeG 0 1, lit₁ := some (uLit 1 false), lit₂ := some (uLit 0 true) }

/-- No marked source belongs to `U`. -/
noncomputable def unreachK3 :
    KromClause (Language.stGraph.sum Language.order) uBlock 3 :=
  { guard := sourceG 0, lit₁ := some (uLit 0 false), lit₂ := none }

/-- The Krom program defining UNREACH. -/
noncomputable def unreachKromProgram :
    KromProgram (Language.stGraph.sum Language.order) uBlock 3 :=
  [unreachK1, unreachK2, unreachK3]

section KromProgram

variable {A : Type} [Language.stGraph.Structure A] [LinearOrder A]

/-- The set guessed by an assignment of the block. -/
def URel (ρ : uBlock.Assignment A) (x : A) : Prop := ρ () ![x]

omit [Language.stGraph.Structure A] [LinearOrder A] in
private theorem uLit_holds (ρ : uBlock.Assignment A) (v : Fin 3 → A) (i : Fin 3)
    (pos : Bool) : (uLit i pos).Holds ρ v ↔ (if pos then URel ρ (v i) else ¬URel ρ (v i)) := by
  have hatom : (uAtom i).Holds ρ v ↔ URel ρ (v i) := by
    refine iff_of_eq (congrArg (ρ ()) (funext fun l => ?_))
    fin_cases l
    rfl
  cases pos with
  | false => exact not_congr hatom
  | true => exact hatom

private theorem realize_edgeG' (v : Fin 3 → A) (i j : Fin 3) :
    (edgeG i j).Realize v ↔ SGEdge (v i) (v j) := by
  rw [edgeG, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

private theorem realize_sourceG' (v : Fin 3 → A) (i : Fin 3) :
    (sourceG i).Realize v ↔ SGSource (v i) := by
  rw [sourceG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

private theorem realize_targetG' (v : Fin 3 → A) (i : Fin 3) :
    (targetG i).Realize v ↔ SGTarget (v i) := by
  rw [targetG, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

/-- What it means for an assignment to satisfy the Krom program: the guessed
set contains the marked targets, is closed under predecessors, and avoids the
marked sources. -/
theorem unreachKromProgram_holds_iff (ρ : uBlock.Assignment A) :
    unreachKromProgram.Holds ρ ↔
      (∀ x : A, SGTarget x → URel ρ x) ∧
      (∀ x y : A, SGEdge x y → URel ρ y → URel ρ x) ∧
      (∀ x : A, SGSource x → ¬URel ρ x) := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun x y hxy hy => ?_, fun x hx hu => ?_⟩
    · have hcl := h ![x, x, x] unreachK1 (by simp [unreachKromProgram])
      have := hcl ((realize_targetG' _ 0).mpr hx)
      simp only [unreachK1, KromLit.slotHolds, Option.elim_some, Option.elim_none,
        or_false] at this
      simpa using (uLit_holds ρ _ 0 true).mp this
    · have hcl := h ![x, y, x] unreachK2 (by simp [unreachKromProgram])
      have := hcl ((realize_edgeG' _ 0 1).mpr hxy)
      simp only [unreachK2, KromLit.slotHolds, Option.elim_some] at this
      rcases this with hneg | hpos
      · exact absurd (by simpa using hy) ((uLit_holds ρ _ 1 false).mp hneg)
      · simpa using (uLit_holds ρ _ 0 true).mp hpos
    · have hcl := h ![x, x, x] unreachK3 (by simp [unreachKromProgram])
      have := hcl ((realize_sourceG' _ 0).mpr hx)
      simp only [unreachK3, KromLit.slotHolds, Option.elim_some, Option.elim_none,
        or_false] at this
      exact (uLit_holds ρ _ 0 false).mp this (by simpa using hu)
  · rintro ⟨h1, h2, h3⟩ v c hc
    simp only [unreachKromProgram, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · intro hg
      refine Or.inl ?_
      simp only [unreachK1, KromLit.slotHolds, Option.elim_some]
      exact (uLit_holds ρ _ 0 true).mpr (h1 _ ((realize_targetG' _ 0).mp hg))
    · intro hg
      by_cases hy : URel ρ (v 1)
      · refine Or.inr ?_
        simp only [unreachK2, KromLit.slotHolds, Option.elim_some]
        exact (uLit_holds ρ _ 0 true).mpr (h2 _ _ ((realize_edgeG' _ 0 1).mp hg) hy)
      · refine Or.inl ?_
        simp only [unreachK2, KromLit.slotHolds, Option.elim_some]
        exact (uLit_holds ρ _ 1 false).mpr hy
    · intro hg
      refine Or.inl ?_
      simp only [unreachK3, KromLit.slotHolds, Option.elim_some]
      exact (uLit_holds ρ _ 0 false).mpr (h3 _ ((realize_sourceG' _ 0).mp hg))

/-- The set of vertices from which a marked target is reachable: the witness
of the nontrivial direction. -/
def coReachAssign : uBlock.Assignment A :=
  fun _ w => ∃ t : A, SGTarget t ∧ Relation.ReflTransGen SGEdge (w ⟨0, Nat.zero_lt_one⟩) t

omit [LinearOrder A] in
@[simp]
theorem uRel_coReachAssign (x : A) :
    URel (coReachAssign (A := A)) x ↔ ∃ t : A, SGTarget t ∧ Relation.ReflTransGen SGEdge x t :=
  Iff.rfl

omit [LinearOrder A] in
/-- A set closed under predecessors and containing the marked targets contains
every vertex from which a marked target is reachable. -/
theorem uRel_of_reflTransGen {ρ : uBlock.Assignment A}
    (h2 : ∀ x y : A, SGEdge x y → URel ρ y → URel ρ x) {x y : A}
    (h : Relation.ReflTransGen SGEdge x y) : URel ρ y → URel ρ x := by
  induction h with
  | refl => exact id
  | tail _ hbc ih => exact fun hc => ih (h2 _ _ hbc hc)

end KromProgram

/-- **UNREACH is SO-Krom definable**: guess the set of vertices from which a
marked target is reachable. The clauses are two-literal – the closure rule is
`¬U(y) ∨ U(x)` – so no transitive closure has to be built, unlike in the Horn
program above. -/
theorem unreach_sigmaSOKromDefinable : SigmaSOKromDefinable UNREACH := by
  refine ⟨uBlock, 3, unreachKromProgram, ?_⟩
  intro A _ _ _ _
  constructor
  · intro h
    refine ⟨coReachAssign, (unreachKromProgram_holds_iff _).mpr
      ⟨fun x hx => ⟨x, hx, Relation.ReflTransGen.refl⟩, fun x y hxy hy => ?_, fun x hx hu => ?_⟩⟩
    · obtain ⟨t, ht, hpath⟩ := hy
      exact ⟨t, ht, Relation.ReflTransGen.head hxy hpath⟩
    · obtain ⟨t, ht, hpath⟩ := hu
      exact h ⟨x, t, hx, ht, hpath⟩
  · rintro ⟨ρ, hρ⟩ ⟨s, t, hs, ht, hpath⟩
    obtain ⟨h1, h2, h3⟩ := (unreachKromProgram_holds_iff ρ).mp hρ
    exact h3 s hs (uRel_of_reflTransGen h2 hpath (h1 t ht))

/-- **UNREACH is in NL**, by definition of the class as SO-Krom
definability. -/
theorem unreach_mem_NL : UNREACH ∈ NL :=
  unreach_sigmaSOKromDefinable

/-! ### REACH is FO(TC) definable

The canonical example of `DescriptiveComplexity.TCDefinable`, and the one the logic is
shaped after: REACH *is* a transitive closure, at arity one, of the edge
relation between the marked sources and the marked targets. Note the contrast
with the two clausal fragments above, which define the *complement* head-on:
here it is reachability itself that is stated, which is why closing FO(TC)
under complement (Immerman–Szelepcsényi) is what `REACH ∈ NL` waits on. -/

/-- The transition formula of the walk: an edge from the current vertex to the
next one. -/
noncomputable def tcEdgeF :
    (Language.stGraph.sum Language.order).Formula (Fin 1 ⊕ Fin 1) :=
  Relations.formula₂ sgEdgeO (Term.var (Sum.inl 0)) (Term.var (Sum.inr 0))

/-- The starting tuples of the walk: the marked sources. -/
noncomputable def tcSourceF : (Language.stGraph.sum Language.order).Formula (Fin 1) :=
  Relations.formula₁ sgSourceO (Term.var 0)

/-- The accepting tuples of the walk: the marked targets. -/
noncomputable def tcTargetF : (Language.stGraph.sum Language.order).Formula (Fin 1) :=
  Relations.formula₁ sgTargetO (Term.var 0)

/-- REACH as a single transitive closure: a walk along edges, from a marked
source to a marked target. -/
noncomputable abbrev reachSpec : TCSpec Language.stGraph where
  k := 1
  step := tcEdgeF
  src := tcSourceF
  tgt := tcTargetF

section TCProgram

variable {A : Type} [Language.stGraph.Structure A] [LinearOrder A]

@[simp]
theorem step_reachSpec (a b : Fin 1 → A) :
    reachSpec.Step a b ↔ SGEdge (a 0) (b 0) := by
  change tcEdgeF.Realize (Sum.elim a b) ↔ _
  rw [tcEdgeF, Formula.realize_rel₂, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_tcSourceF (v : Fin 1 → A) : tcSourceF.Realize v ↔ SGSource (v 0) := by
  rw [tcSourceF, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

@[simp]
theorem realize_tcTargetF (v : Fin 1 → A) : tcTargetF.Realize v ↔ SGTarget (v 0) := by
  rw [tcTargetF, Formula.realize_rel₁, relMap_sumInl]
  exact Iff.rfl

/-- A path in the graph is a walk of the specification. -/
theorem reach_of_reflTransGen {x y : A} (h : Relation.ReflTransGen SGEdge x y) :
    reachSpec.Reach (fun _ => x) (fun _ => y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact ih.tail ((step_reachSpec (fun _ => b) fun _ => c).mpr hbc)

/-- A walk of the specification is a path in the graph. -/
theorem reflTransGen_of_reach {u v : Fin 1 → A} (h : reachSpec.Reach u v) :
    Relation.ReflTransGen SGEdge (u 0) (v 0) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact ih.tail ((step_reachSpec b c).mp hbc)

end TCProgram

/-- **REACH is FO(TC) definable**: it is a single transitive closure of the
edge relation, at arity one. -/
theorem reach_tcDefinable : TCDefinable REACH := by
  refine ⟨reachSpec, ?_⟩
  intro A _ _ _ _
  constructor
  · rintro ⟨s, t, hs, ht, hpath⟩
    exact ⟨fun _ => s, fun _ => t, (realize_tcSourceF _).mpr hs,
      (realize_tcTargetF _).mpr ht, reach_of_reflTransGen hpath⟩
  · rintro ⟨u, v, hu, hv, huv⟩
    exact ⟨u 0, v 0, (realize_tcSourceF u).mp hu, (realize_tcTargetF v).mp hv,
      reflTransGen_of_reach huv⟩

end DescriptiveComplexity
