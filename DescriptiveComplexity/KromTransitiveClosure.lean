/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.KromImplication
import DescriptiveComplexity.ClauseDischarge
import DescriptiveComplexity.TransitiveClosureKrom

/-!
# From the Krom fragment to FO(TC), through the complement

The formula layer of the converse translation: the implication graph of a Krom
program, walked by a `DescriptiveComplexity.TCSpec`.

`DescriptiveComplexity.KromImpl.exists_holds_iff` says that a Krom program is
satisfiable exactly when no goal clause fires and no literal reaches its own
negation and back, and `DescriptiveComplexity.TwoCnf.carryReach_iff` turns the second
condition – a *conjunction* of two reachabilities – into a single walk of the
cycle-witnessing graph, on nodes carrying the start literal, the current one
and a flag. This file expresses that walk as first-order data:

* a node's two literals are two *modes* (a relation variable of the block and a
  sign, twice) together with two tuples of dimension
  `DescriptiveComplexity.clauseDim`, holding the canonically padded arguments of the
  two atoms – the same encoding the Horn and Krom discharges use;
* the flag is a third component of the mode;
* an edge of the implication graph is
  `DescriptiveComplexity.KromTC.edgeCaseF`: for one clause of the program and one choice
  of which of its literal slots is the source and which the target, the clause's
  guard holds at some valuation of its `k` variables, and the two node tuples
  hold the canonically padded arguments of the two atoms at that valuation.
  Quantifying the valuation existentially and taking the disjunction over the
  program gives the transition formula.

The walk starts at a node whose two literals agree and whose flag is down, and
accepts when they agree again with the flag up; one extra mode accepts
reflexively when a goal clause fires, the empty clause of the 2-CNF. So the
specification accepts exactly when the program is unsatisfiable
(`DescriptiveComplexity.KromTC.accepts_iff_not_exists_holds`), which is
`DescriptiveComplexity.TCDefinable.compl_of_sigmaSOKromDefinable`: **the complement of
an SO-Krom definable problem is FO(TC) definable**. With the direction proved
in `DescriptiveComplexity.TransitiveClosureKrom` this is an equivalence,
`co-NL(Krom) = NL(TC)` (`DescriptiveComplexity.mem_NL_iff_tcDefinable_compl`); what it
is *not* is `REACH ∈ NL`, which needs the complementation of FO(TC) itself
(Immerman–Szelepcsényi).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

namespace KromTC

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ}

/-! ### The two halves of a node's tuple -/

/-- The first half of a node's tuple: the arguments of the start literal's
atom. -/
abbrev fstHalf (D : ℕ) : Fin D → Fin (D + D) := Fin.castAdd D

/-- The second half of a node's tuple: the arguments of the current literal's
atom. -/
abbrev sndHalf (D : ℕ) : Fin D → Fin (D + D) := Fin.natAdd D

/-! ### The edge formula -/

section Formulas

variable {γ : Type}

/-- One way for a clause to contribute an edge: its guard holds at some
valuation of its `k` universally quantified variables, the coordinates selected
by `u` hold the canonically padded arguments of the source atom at that
valuation, and those selected by `w` hold the arguments of the target atom. -/
noncomputable def edgeCaseF (c : KromClause (L.sum Language.order) B k)
    (a₁ a₂ : SOAtom B k) (u w : Fin (clauseDim B k) → γ) :
    (L.sum Language.order).Formula γ :=
  ((guardF (B := B) c.guard (fun j => Sum.inr j) ⊓
      atomOccF (L := L) a₁ (fun j => Sum.inr j) fun j => Sum.inl (u j)) ⊓
    atomOccF (L := L) a₂ (fun j => Sum.inr j) fun j => Sum.inl (w j)).iExs
    (Fin (clauseDim B k))

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

theorem realize_edgeCaseF {c : KromClause (L.sum Language.order) B k} {a₁ a₂ : SOAtom B k}
    {u w : Fin (clauseDim B k) → γ} :
    (edgeCaseF c a₁ a₂ u w).Realize v ↔
      ∃ t : Fin (clauseDim B k) → A,
        c.guard.Realize (fun j => t (Fin.castLE le_clauseDim j)) ∧
          PadTup (atomIdx a₁) t (fun j => v (u j)) ∧
            PadTup (atomIdx a₂) t fun j => v (w j) := by
  rw [edgeCaseF]
  simp only [Formula.realize_iExs, Formula.realize_inf, realize_guardF, realize_atomOccF,
    Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨t, ⟨hg, h₁⟩, h₂⟩ => ⟨t, hg, h₁, h₂⟩, fun ⟨t, hg, h₁, h₂⟩ => ⟨t, ⟨hg, h₁⟩, h₂⟩⟩

end Formulas

/-! ### The literal a node denotes -/

section Decode

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The literal denoted by a relation variable, a sign and a tuple: the atom
holds the first `B.arity i` coordinates. -/
noncomputable def litAt (i : B.ι) (s : Bool) (w : Fin (clauseDim B k) → A) :
    TwoCnf.Lit (KromImpl.KromAtom B A) :=
  (⟨i, pref (arity_le_clauseDim (k := k) i) w⟩, s)

omit [LinearOrder A] in
@[simp]
theorem litAt_fst_fst (i : B.ι) (s : Bool) (w : Fin (clauseDim B k) → A) :
    (litAt (k := k) i s w).1.1 = i := rfl

omit [LinearOrder A] in
@[simp]
theorem litAt_snd (i : B.ι) (s : Bool) (w : Fin (clauseDim B k) → A) :
    (litAt (k := k) i s w).2 = s := rfl

/-- The literal of a Krom literal, read at the prefix of a clause tuple, is the
literal its atom denotes at the canonical padding of its arguments. -/
theorem litAt_pad {a₀ : A} (ha₀ : IsBot a₀) (l : KromLit B k)
    (t : Fin (clauseDim B k) → A) {x : Fin (clauseDim B k) → A}
    (hpad : PadTup (atomIdx l.atom) t x) :
    litAt l.atom.idx l.positive x =
      KromImpl.litOf l fun j => t (Fin.castLE (le_clauseDim (B := B)) j) := by
  rw [litAt, KromImpl.litOf, KromImpl.atomVar, eq_pad_of_padTup ha₀ hpad, pref_pad]
  rfl

end Decode

/-! ### The edges a clause contributes -/

section ClauseEdge

variable {γ : Type}

open Classical in
/-- All the ways one clause contributes an edge from the literal `(i, s)` to
the literal `(j, t)`. -/
noncomputable def clauseEdgeF (c : KromClause (L.sum Language.order) B k) (i j : B.ι)
    (s t : Bool) (u w : Fin (clauseDim B k) → γ) : (L.sum Language.order).Formula γ :=
  listSup ((KromImpl.edgePairs c).map fun pr =>
    if pr.1.atom.idx = i ∧ pr.1.positive = !s ∧ pr.2.atom.idx = j ∧ pr.2.positive = t then
      edgeCaseF c pr.1.atom pr.2.atom u w
    else ⊥)

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

theorem realize_clauseEdgeF {c : KromClause (L.sum Language.order) B k} {i j : B.ι}
    {s t : Bool} {u w : Fin (clauseDim B k) → γ} :
    (clauseEdgeF c i j s t u w).Realize v ↔
      ∃ pr ∈ KromImpl.edgePairs c,
        pr.1.atom.idx = i ∧ pr.1.positive = !s ∧ pr.2.atom.idx = j ∧ pr.2.positive = t ∧
          ∃ tv : Fin (clauseDim B k) → A,
            c.guard.Realize (fun m => tv (Fin.castLE le_clauseDim m)) ∧
              PadTup (atomIdx pr.1.atom) tv (fun m => v (u m)) ∧
                PadTup (atomIdx pr.2.atom) tv fun m => v (w m) := by
  classical
  rw [clauseEdgeF, realize_listSup]
  constructor
  · rintro ⟨ψ, hψmem, hψ⟩
    obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp hψmem
    by_cases hcond : pr.1.atom.idx = i ∧ pr.1.positive = !s ∧ pr.2.atom.idx = j ∧
        pr.2.positive = t
    · rw [if_pos hcond, realize_edgeCaseF] at hψ
      exact ⟨pr, hpr, hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2, hψ⟩
    · rw [if_neg hcond] at hψ
      exact hψ.elim
  · rintro ⟨pr, hpr, h₁, h₂, h₃, h₄, hex⟩
    refine ⟨_, List.mem_map.mpr ⟨pr, hpr, rfl⟩, ?_⟩
    rw [if_pos ⟨h₁, h₂, h₃, h₄⟩, realize_edgeCaseF]
    exact hex

end ClauseEdge

/-! ### The edges of the program

The transition formula proper: the disjunction over the program of the edges
each clause contributes. Its realization is a step of the implication graph of
`DescriptiveComplexity.KromImpl.clauseRel`, together with the canonicity of the two node
tuples – which the formula forces, each disjunct pinning both tuples to the
padded arguments of its atoms. -/

section ProgramEdge

/-- Decoding a node tuple from the literal it denotes: under canonicity, the
tuple *is* the canonical padding of the literal's arguments. -/
theorem eq_pad_of_litAt_eq {A : Type} [LinearOrder A] {a₀ : A}
    (ha₀ : IsBot a₀) {i : B.ι} {s : Bool} {x : Fin (clauseDim B k) → A} {l : KromLit B k}
    {vv : Fin k → A} (hcan : Canon (B.arity i) x) (h : litAt i s x = KromImpl.litOf l vv) :
    l.atom.idx = i ∧ l.positive = s ∧ x = pad a₀ fun m => vv (l.atom.args m) := by
  have hsig : (⟨i, pref (arity_le_clauseDim (k := k) i) x⟩ : KromImpl.KromAtom B A) =
      ⟨l.atom.idx, fun m => vv (l.atom.args m)⟩ := congrArg Prod.fst h
  have hsgn : s = l.positive := congrArg Prod.snd h
  rw [Sigma.mk.injEq] at hsig
  obtain ⟨hidx, hargs⟩ := hsig
  subst hidx
  refine ⟨rfl, hsgn.symm, ?_⟩
  rw [← eq_of_heq hargs, pad_pref_of_canon ha₀ _ hcan]

variable {γ : Type}

/-- The edge relation of the whole program, from the literal `(i, s)` to the
literal `(j, t)`. -/
noncomputable def edgeF (prog : KromProgram (L.sum Language.order) B k) (i j : B.ι)
    (s t : Bool) (u w : Fin (clauseDim B k) → γ) : (L.sum Language.order).Formula γ :=
  listSup (prog.map fun c => clauseEdgeF c i j s t u w)

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] {v : γ → A}

/-- **The transition formula is the implication graph**: it holds exactly when
both node tuples are canonically padded and the literals they denote form an
edge. -/
theorem realize_edgeF {prog : KromProgram (L.sum Language.order) B k} {i j : B.ι}
    {s t : Bool} {u w : Fin (clauseDim B k) → γ} :
    (edgeF prog i j s t u w).Realize v ↔
      Canon (B.arity i) (fun m => v (u m)) ∧ Canon (B.arity j) (fun m => v (w m)) ∧
        TwoCnf.Step (KromImpl.clauseRel prog) (litAt i s fun m => v (u m))
          (litAt j t fun m => v (w m)) := by
  classical
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  rw [edgeF, realize_listSup]
  constructor
  · rintro ⟨ψ, hψmem, hψ⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hψmem
    obtain ⟨pr, hpr, hidx₁, hpos₁, hidx₂, hpos₂, tv, hg, hpad₁, hpad₂⟩ :=
      realize_clauseEdgeF.mp hψ
    have hlit₁ := litAt_pad ha₀ pr.1 tv hpad₁
    have hlit₂ := litAt_pad ha₀ pr.2 tv hpad₂
    have hx₁ := eq_pad_of_padTup ha₀ hpad₁
    have hx₂ := eq_pad_of_padTup ha₀ hpad₂
    subst hidx₁
    subst hidx₂
    refine ⟨by rw [hx₁]; exact canon_pad ha₀ _ _, by rw [hx₂]; exact canon_pad ha₀ _ _, ?_⟩
    refine (KromImpl.step_iff_edgePairs prog _ _).mpr
      ⟨c, hc, (fun m => tv (Fin.castLE (le_clauseDim (B := B)) m)), hg, pr, hpr, ?_, ?_⟩
    · rw [← hlit₁, TwoCnf.neg, hpos₁]
      simp [litAt]
    · rw [← hlit₂, hpos₂]
  · rintro ⟨hcan₁, hcan₂, hstep⟩
    obtain ⟨c, hc, vv, hg, pr, hpr, hp, hq⟩ :=
      (KromImpl.step_iff_edgePairs prog _ _).mp hstep
    have hp' : litAt i (!s) (fun m => v (u m)) = KromImpl.litOf pr.1 vv := by
      rw [← hp, TwoCnf.neg]
      simp [litAt]
    obtain ⟨hidx₁, hpos₁, hx₁⟩ := eq_pad_of_litAt_eq ha₀ hcan₁ hp'
    obtain ⟨hidx₂, hpos₂, hx₂⟩ := eq_pad_of_litAt_eq ha₀ hcan₂ hq
    refine ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, realize_clauseEdgeF.mpr
      ⟨pr, hpr, hidx₁, ?_, hidx₂, hpos₂, pad a₀ vv, ?_, ?_, ?_⟩⟩
    · exact hpos₁
    · have hpref : (fun m => pad (D := clauseDim B k) a₀ vv
          (Fin.castLE (le_clauseDim (B := B)) m)) = vv :=
        pref_pad a₀ (le_clauseDim (B := B)) vv
      rw [hpref]
      exact hg
    · rw [hx₁]
      have : (fun m => pad (D := clauseDim B k) a₀ vv (atomIdx pr.1.atom m)) =
          fun m => vv (pr.1.atom.args m) := by
        funext m
        exact congrFun (pref_pad a₀ (le_clauseDim (B := B)) vv) (pr.1.atom.args m)
      rw [← this]
      exact padTup_pad ha₀ _ _
    · rw [hx₂]
      have : (fun m => pad (D := clauseDim B k) a₀ vv (atomIdx pr.2.atom m)) =
          fun m => vv (pr.2.atom.args m) := by
        funext m
        exact congrFun (pref_pad a₀ (le_clauseDim (B := B)) vv) (pr.2.atom.args m)
      rw [← this]
      exact padTup_pad ha₀ _ _

end ProgramEdge

/-! ### The specification

The nodes of the walk are the nodes of the cycle-witnessing graph of
`DescriptiveComplexity.TwoCnf.carryReach_iff`: the start literal, the current literal
and a flag. The two literals' relation variables and signs, and the flag, are
the *mode*; their arguments are the two halves of the tuple. One extra mode
accepts reflexively when a goal clause fires. -/

section Spec

variable (prog : KromProgram (L.sum Language.order) B k)

/-- A literal's share of a mode: a relation variable of the block and a
sign. -/
abbrev LitMode (B : SOBlock) : Type := B.ι × Bool

/-- The modes of the walk: the two literals' shares and the flag, or the mode
that reports a firing goal clause. -/
abbrev Mode (B : SOBlock) : Type := (LitMode B × LitMode B × Bool) ⊕ Unit

section Formulas

variable {γ : Type}

open Classical in
/-- Some goal clause of the program fires. -/
noncomputable def goalF : (L.sum Language.order).Formula γ :=
  listSup (prog.map fun c =>
    if c.lit₁ = none ∧ c.lit₂ = none then
      (guardF (B := B) c.guard fun m => Sum.inr m).iExs (Fin (clauseDim B k))
    else ⊥)

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] {v : γ → A}

omit [Finite A] in
theorem realize_goalF : (goalF prog).Realize v ↔ KromImpl.GoalFires prog A := by
  classical
  obtain ⟨a₀⟩ : Nonempty A := inferInstance
  rw [goalF, realize_listSup]
  constructor
  · rintro ⟨ψ, hψmem, hψ⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hψmem
    by_cases hnone : c.lit₁ = none ∧ c.lit₂ = none
    · rw [if_pos hnone, Formula.realize_iExs] at hψ
      obtain ⟨t, ht⟩ := hψ
      rw [realize_guardF] at ht
      exact ⟨c, hc, _, ht, hnone.1, hnone.2⟩
    · rw [if_neg hnone] at hψ
      exact hψ.elim
  · rintro ⟨c, hc, vv, hg, h₁, h₂⟩
    refine ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, ?_⟩
    rw [if_pos ⟨h₁, h₂⟩, Formula.realize_iExs]
    refine ⟨pad a₀ vv, ?_⟩
    rw [realize_guardF]
    have hpref : (fun m => Sum.elim v (pad (D := clauseDim B k) a₀ vv)
        (Sum.inr (Fin.castLE (le_clauseDim (B := B)) m))) = vv :=
      pref_pad a₀ (le_clauseDim (B := B)) vv
    rw [hpref]
    exact hg

end Formulas

open Classical in
/-- The starting nodes: the current literal is the start, the flag is down, and
both halves of the tuple are the same canonical padding – or a firing goal
clause, in the reporting mode. -/
noncomputable def srcF : Mode B →
    (L.sum Language.order).Formula (Fin (clauseDim B k + clauseDim B k))
  | Sum.inl ((i, s), (j, t), ph) =>
      if (i, s) = (j, t) ∧ ph = false then
        (eqTupF (fstHalf (clauseDim B k)) (sndHalf (clauseDim B k)) ⊓
          canonF (B.arity i) (fstHalf (clauseDim B k))) ⊓
          canonF (B.arity i) (sndHalf (clauseDim B k))
      else ⊥
  | Sum.inr () => goalF prog

open Classical in
/-- The accepting nodes: the current literal is the start again, with the flag
up – or a firing goal clause. -/
noncomputable def tgtF : Mode B →
    (L.sum Language.order).Formula (Fin (clauseDim B k + clauseDim B k))
  | Sum.inl ((i, s), (j, t), ph) =>
      if (i, s) = (j, t) ∧ ph = true then
        eqTupF (fstHalf (clauseDim B k)) (sndHalf (clauseDim B k))
      else ⊥
  | Sum.inr () => goalF prog

/-- The payload of a walk mode: the two literals' shares and the flag. -/
abbrev Walk (B : SOBlock) : Type := LitMode B × LitMode B × Bool

open Classical in
/-- One step between two walk modes, as a formula on the two nodes' tuples:
the start is kept, the current literal moves along an edge of the implication
graph, and the flag may go up only on arrival at the negation of the start.

Stated on the *payloads* rather than on `DescriptiveComplexity.KromTC.Mode`, so that its
realization lemma applies without unfolding a match. -/
noncomputable def stepWalkF (p q : Walk B) :
    (L.sum Language.order).Formula
      (Fin (clauseDim B k + clauseDim B k) ⊕ Fin (clauseDim B k + clauseDim B k)) :=
  if q.1 = p.1 ∧
      (q.2.2 = p.2.2 ∨ (p.2.2 = false ∧ q.2.2 = true ∧ q.2.1 = (p.1.1, !p.1.2))) then
    (eqTupF (fun m => Sum.inl (fstHalf (clauseDim B k) m))
        (fun m => Sum.inr (fstHalf (clauseDim B k) m)) ⊓
      edgeF prog p.2.1.1 q.2.1.1 p.2.1.2 q.2.1.2
        (fun m => Sum.inl (sndHalf (clauseDim B k) m))
        fun m => Sum.inr (sndHalf (clauseDim B k) m)) ⊓
      (if p.2.2 = false ∧ q.2.2 = true then
        eqTupF (fun m => Sum.inr (fstHalf (clauseDim B k) m))
          fun m => Sum.inr (sndHalf (clauseDim B k) m)
      else ⊤)
  else ⊥

/-- One step: a step between walk modes, and nothing into or out of the mode
that reports a firing goal clause. -/
noncomputable def stepF : Mode B → Mode B →
    (L.sum Language.order).Formula
      (Fin (clauseDim B k + clauseDim B k) ⊕ Fin (clauseDim B k + clauseDim B k))
  | Sum.inl p, Sum.inl q => stepWalkF prog p q
  | _, _ => ⊥

section StepRealize

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- Realization of a step between walk modes, spelled out. -/
theorem realize_stepWalkF {p q : Walk B}
    {x y : Fin (clauseDim B k + clauseDim B k) → A} :
    (stepWalkF prog p q).Realize (Sum.elim x y) ↔
      (q.1 = p.1 ∧
        (q.2.2 = p.2.2 ∨ (p.2.2 = false ∧ q.2.2 = true ∧ q.2.1 = (p.1.1, !p.1.2)))) ∧
      ((fun m => y (fstHalf (clauseDim B k) m)) = fun m => x (fstHalf (clauseDim B k) m)) ∧
      Canon (B.arity p.2.1.1) (fun m => x (sndHalf (clauseDim B k) m)) ∧
      Canon (B.arity q.2.1.1) (fun m => y (sndHalf (clauseDim B k) m)) ∧
      TwoCnf.Step (KromImpl.clauseRel prog)
        (litAt p.2.1.1 p.2.1.2 fun m => x (sndHalf (clauseDim B k) m))
        (litAt q.2.1.1 q.2.1.2 fun m => y (sndHalf (clauseDim B k) m)) ∧
      (p.2.2 = false → q.2.2 = true →
        (fun m => y (sndHalf (clauseDim B k) m)) = fun m => y (fstHalf (clauseDim B k) m)) := by
  classical
  rw [stepWalkF]
  by_cases hmode : q.1 = p.1 ∧
      (q.2.2 = p.2.2 ∨ (p.2.2 = false ∧ q.2.2 = true ∧ q.2.1 = (p.1.1, !p.1.2)))
  · rw [if_pos hmode]
    by_cases hflip : p.2.2 = false ∧ q.2.2 = true
    · rw [if_pos hflip]
      simp only [Formula.realize_inf, realize_eqTupF, realize_edgeF, Sum.elim_inl,
        Sum.elim_inr]
      constructor
      · rintro ⟨⟨hs, hc₁, hc₂, hst⟩, hf⟩
        exact ⟨hmode, hs, hc₁, hc₂, hst, fun _ _ => hf⟩
      · rintro ⟨-, hs, hc₁, hc₂, hst, hf⟩
        exact ⟨⟨hs, hc₁, hc₂, hst⟩, hf hflip.1 hflip.2⟩
    · rw [if_neg hflip]
      simp only [Formula.realize_inf, realize_eqTupF, realize_edgeF, Formula.realize_top,
        and_true, Sum.elim_inl, Sum.elim_inr]
      constructor
      · rintro ⟨hs, hc₁, hc₂, hst⟩
        refine ⟨hmode, hs, hc₁, hc₂, hst, fun h₁ h₂ => ?_⟩
        exact absurd (show p.2.2 = false ∧ q.2.2 = true from ⟨h₁, h₂⟩) hflip
      · rintro ⟨-, hs, hc₁, hc₂, hst, -⟩
        exact ⟨hs, hc₁, hc₂, hst⟩
  · rw [if_neg hmode]
    constructor
    · exact fun h => h.elim
    · rintro ⟨hm, -⟩
      exact absurd hm hmode

end StepRealize

/-- The specification: the cycle-witnessing walk of the program's implication
graph, plus the mode reporting a firing goal clause. -/
noncomputable abbrev spec : TCSpec L where
  Mode := Mode B
  k := clauseDim B k + clauseDim B k
  step := stepF prog
  src := srcF prog
  tgt := tgtF prog

section SpecSteps

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

omit [Finite A] [Nonempty A] in
/-- Realization of a step of the specification, between walk modes. -/
theorem step_spec_walk_iff {p q : Walk B}
    {x y : Fin (clauseDim B k + clauseDim B k) → A} :
    (spec prog).Step (Sum.inl p, x) (Sum.inl q, y) ↔
      (stepWalkF prog p q).Realize (Sum.elim x y) :=
  Iff.rfl

omit [Finite A] [Nonempty A] in
/-- There is no step out of the goal-reporting mode. -/
theorem not_step_goal_left {q : Mode B} {x y : Fin (clauseDim B k + clauseDim B k) → A} :
    ¬(spec prog).Step (Sum.inr (), x) (q, y) := by
  cases q <;> exact id

omit [Finite A] [Nonempty A] in
/-- There is no step into the goal-reporting mode. -/
theorem not_step_goal_right {p : Mode B} {x y : Fin (clauseDim B k + clauseDim B k) → A} :
    ¬(spec prog).Step (p, x) (Sum.inr (), y) := by
  cases p <;> exact id

end SpecSteps

/-! ### Nodes and carry nodes -/

section Nodes

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- The carry node a walk node denotes. -/
noncomputable def decodeNode (p : Walk B) (x : Fin (clauseDim B k + clauseDim B k) → A) :
    TwoCnf.CarryNode (KromImpl.KromAtom B A) :=
  (litAt p.1.1 p.1.2 (fun m => x (fstHalf (clauseDim B k) m)),
    litAt p.2.1.1 p.2.1.2 (fun m => x (sndHalf (clauseDim B k) m)), p.2.2)

/-- The walk mode of a carry node. -/
def modeOf (n : TwoCnf.CarryNode (KromImpl.KromAtom B A)) : Walk B :=
  ((n.1.1.1, n.1.2), (n.2.1.1.1, n.2.1.2), n.2.2)

/-- The tuple of a carry node: the two atoms, canonically padded. -/
noncomputable def tupleOf (a₀ : A) (n : TwoCnf.CarryNode (KromImpl.KromAtom B A)) :
    Fin (clauseDim B k + clauseDim B k) → A :=
  Fin.addCases (pad a₀ n.1.1.2) (pad a₀ n.2.1.1.2)

omit [LinearOrder A] [Finite A] [Nonempty A] in
@[simp]
theorem tupleOf_fstHalf (a₀ : A) (n : TwoCnf.CarryNode (KromImpl.KromAtom B A))
    (m : Fin (clauseDim B k)) : tupleOf a₀ n (fstHalf (clauseDim B k) m) = pad a₀ n.1.1.2 m :=
  Fin.addCases_left _

omit [LinearOrder A] [Finite A] [Nonempty A] in
@[simp]
theorem tupleOf_sndHalf (a₀ : A) (n : TwoCnf.CarryNode (KromImpl.KromAtom B A))
    (m : Fin (clauseDim B k)) :
    tupleOf a₀ n (sndHalf (clauseDim B k) m) = pad a₀ n.2.1.1.2 m :=
  Fin.addCases_right _

omit [LinearOrder A] [Finite A] [Nonempty A] in
@[simp]
theorem modeOf_fst (n : TwoCnf.CarryNode (KromImpl.KromAtom B A)) :
    (modeOf n).1 = (n.1.1.1, n.1.2) := rfl

omit [LinearOrder A] [Finite A] [Nonempty A] in
@[simp]
theorem modeOf_snd_fst (n : TwoCnf.CarryNode (KromImpl.KromAtom B A)) :
    (modeOf n).2.1 = (n.2.1.1.1, n.2.1.2) := rfl

omit [LinearOrder A] [Finite A] [Nonempty A] in
@[simp]
theorem modeOf_snd_snd (n : TwoCnf.CarryNode (KromImpl.KromAtom B A)) :
    (modeOf n).2.2 = n.2.2 := rfl

omit [LinearOrder A] [Finite A] [Nonempty A] in
@[simp]
theorem decodeNode_fst (p : Walk B) (x : Fin (clauseDim B k + clauseDim B k) → A) :
    (decodeNode p x).1 = litAt p.1.1 p.1.2 fun m => x (fstHalf (clauseDim B k) m) := rfl

omit [LinearOrder A] [Finite A] [Nonempty A] in
@[simp]
theorem decodeNode_snd_fst (p : Walk B) (x : Fin (clauseDim B k + clauseDim B k) → A) :
    (decodeNode p x).2.1 = litAt p.2.1.1 p.2.1.2 fun m => x (sndHalf (clauseDim B k) m) := rfl

omit [LinearOrder A] [Finite A] [Nonempty A] in
@[simp]
theorem decodeNode_snd_snd (p : Walk B) (x : Fin (clauseDim B k + clauseDim B k) → A) :
    (decodeNode p x).2.2 = p.2.2 := rfl

omit [LinearOrder A] [Finite A] [Nonempty A] in
theorem litAt_pad_self (a₀ : A) (p : TwoCnf.Lit (KromImpl.KromAtom B A)) :
    litAt p.1.1 p.2 (pad (D := clauseDim B k) a₀ p.1.2) = p := by
  rw [litAt, pref_pad]
  rfl

omit [LinearOrder A] [Finite A] [Nonempty A] in
/-- Decoding the encoding gives the carry node back. -/
theorem decodeNode_tupleOf (a₀ : A) (n : TwoCnf.CarryNode (KromImpl.KromAtom B A)) :
    decodeNode (k := k) (modeOf n) (tupleOf (k := k) a₀ n) = n := by
  have h₁ : (fun m => tupleOf a₀ n (fstHalf (clauseDim B k) m)) = pad a₀ n.1.1.2 :=
    funext fun m => tupleOf_fstHalf a₀ n m
  have h₂ : (fun m => tupleOf a₀ n (sndHalf (clauseDim B k) m)) = pad a₀ n.2.1.1.2 :=
    funext fun m => tupleOf_sndHalf a₀ n m
  rw [decodeNode, modeOf, h₁, h₂, litAt_pad_self, litAt_pad_self]

/-- **A carry step lifts to a step of the specification**, at the canonically
padded nodes. -/
theorem step_of_carryStep {a₀ : A} (ha₀ : IsBot a₀)
    {n m : TwoCnf.CarryNode (KromImpl.KromAtom B A)}
    (h : TwoCnf.CarryStep (KromImpl.clauseRel prog) n m) :
    (spec prog).Step (Sum.inl (modeOf n), tupleOf a₀ n) (Sum.inl (modeOf m), tupleOf a₀ m) := by
  obtain ⟨hstart, hstep, hphase⟩ := h
  have hatom : m.1.1 = n.1.1 := congrArg Prod.fst hstart
  have hsign : m.1.2 = n.1.2 := congrArg Prod.snd hstart
  rw [step_spec_walk_iff, realize_stepWalkF]
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- the start mode is kept
    simp only [modeOf_fst, hatom, hsign]
  · -- the flag
    rcases hphase with hph | ⟨hn, hm, hneg⟩
    · exact Or.inl hph
    · refine Or.inr ⟨hn, hm, ?_⟩
      simp only [modeOf_fst, modeOf_snd_fst, hneg, TwoCnf.neg, hstart]
  · -- the start halves agree
    funext j
    rw [tupleOf_fstHalf, tupleOf_fstHalf, hatom]
  · -- both current halves are canonical
    have : (fun j => tupleOf a₀ n (sndHalf (clauseDim B k) j)) = pad a₀ n.2.1.1.2 :=
      funext fun j => tupleOf_sndHalf a₀ n j
    rw [this]
    exact canon_pad ha₀ _ _
  · have : (fun j => tupleOf a₀ m (sndHalf (clauseDim B k) j)) = pad a₀ m.2.1.1.2 :=
      funext fun j => tupleOf_sndHalf a₀ m j
    rw [this]
    exact canon_pad ha₀ _ _
  · -- the current literals form an edge
    have h₁ : (fun j => tupleOf a₀ n (sndHalf (clauseDim B k) j)) = pad a₀ n.2.1.1.2 :=
      funext fun j => tupleOf_sndHalf a₀ n j
    have h₂ : (fun j => tupleOf a₀ m (sndHalf (clauseDim B k) j)) = pad a₀ m.2.1.1.2 :=
      funext fun j => tupleOf_sndHalf a₀ m j
    simp only [modeOf_snd_fst]
    rw [h₁, h₂, litAt_pad_self, litAt_pad_self]
    exact hstep
  · -- when the flag rises, the current literal is the start's negation
    intro h₁ h₂
    rcases hphase with hph | ⟨-, -, hneg⟩
    · simp only [modeOf_snd_snd] at h₁ h₂
      rw [h₁, h₂] at hph
      exact absurd hph (by simp)
    · funext j
      rw [tupleOf_sndHalf, tupleOf_fstHalf, hneg, TwoCnf.neg]

/-- **A step of the specification is a carry step** of the decoded nodes. -/
theorem carryStep_of_step {p q : Walk B} {x y : Fin (clauseDim B k + clauseDim B k) → A}
    (h : (spec prog).Step (Sum.inl p, x) (Sum.inl q, y)) :
    TwoCnf.CarryStep (KromImpl.clauseRel prog) (decodeNode p x) (decodeNode q y) := by
  rw [step_spec_walk_iff, realize_stepWalkF] at h
  obtain ⟨⟨hmode, hph⟩, hstart, -, -, hstep, hflip⟩ := h
  have hidx₀ : q.1.1 = p.1.1 := by rw [hmode]
  have hsgn₀ : q.1.2 = p.1.2 := by rw [hmode]
  refine ⟨?_, hstep, ?_⟩
  · -- the start literals agree
    simp only [decodeNode_fst, hidx₀, hsgn₀, hstart]
  · -- the flag
    rcases hph with hph | ⟨hn, hm, hneg⟩
    · exact Or.inl hph
    · refine Or.inr ⟨hn, hm, ?_⟩
      have hy := hflip hn hm
      have hidx : q.2.1.1 = p.1.1 := by rw [hneg]
      have hsgn : q.2.1.2 = !p.1.2 := by rw [hneg]
      have hcur : litAt q.2.1.1 q.2.1.2 (fun m => y (sndHalf (clauseDim B k) m)) =
          litAt p.1.1 (!p.1.2) fun m => y (fstHalf (clauseDim B k) m) := by
        rw [hidx, hsgn, hy]
      rw [decodeNode_snd_fst, decodeNode_fst, hcur, TwoCnf.neg, litAt, litAt, hidx₀, hsgn₀]

end Nodes

/-! ### Walks -/

section Walks

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **A walk of the cycle-witnessing graph lifts to a walk of the
specification**, at the canonically padded nodes. -/
theorem reach_of_carryReach {a₀ : A} (ha₀ : IsBot a₀)
    {n m : TwoCnf.CarryNode (KromImpl.KromAtom B A)}
    (h : Relation.ReflTransGen (TwoCnf.CarryStep (KromImpl.clauseRel prog)) n m) :
    (spec prog).Reach (Sum.inl (modeOf n), tupleOf a₀ n)
      (Sum.inl (modeOf m), tupleOf a₀ m) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (step_of_carryStep prog ha₀ hstep)

/-- **A walk of the specification out of a walk mode is one of the
cycle-witnessing graph**: the goal-reporting mode is never entered, so every
node along the way decodes to a carry node. -/
theorem carryReach_of_reach {p : Walk B} {x : Fin (clauseDim B k + clauseDim B k) → A}
    {d : (spec prog).Node A} (h : (spec prog).Reach (Sum.inl p, x) d) :
    ∃ (q : Walk B) (y : Fin (clauseDim B k + clauseDim B k) → A), d = (Sum.inl q, y) ∧
      Relation.ReflTransGen (TwoCnf.CarryStep (KromImpl.clauseRel prog))
        (decodeNode p x) (decodeNode q y) := by
  induction h with
  | refl => exact ⟨p, x, rfl, Relation.ReflTransGen.refl⟩
  | @tail c d _ hcd ih =>
    obtain ⟨q, y, hc, hcarry⟩ := ih
    subst hc
    obtain ⟨dm, dy⟩ := d
    cases dm with
    | inr u => exact absurd hcd (not_step_goal_right prog)
    | inl r => exact ⟨r, dy, rfl, hcarry.tail (carryStep_of_step prog hcd)⟩

end Walks

/-! ### The endpoints -/

section Endpoints

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

omit [Finite A] [Nonempty A] in
/-- A walk node is a starting node exactly when its current literal is its
start, its flag is down, and its two halves are the same canonical tuple. -/
theorem isSrc_inl_iff {i j : B.ι} {s t ph : Bool}
    {x : Fin (clauseDim B k + clauseDim B k) → A} :
    (spec prog).IsSrc (Sum.inl ((i, s), (j, t), ph), x) ↔
      (((i, s) : LitMode B) = (j, t) ∧ ph = false) ∧
        ((fun m => x (sndHalf (clauseDim B k) m)) =
          fun m => x (fstHalf (clauseDim B k) m)) ∧
        Canon (B.arity i) (fun m => x (fstHalf (clauseDim B k) m)) ∧
        Canon (B.arity i) (fun m => x (sndHalf (clauseDim B k) m)) := by
  classical
  change (srcF prog (Sum.inl ((i, s), (j, t), ph))).Realize x ↔ _
  rw [srcF]
  by_cases hc : ((i, s) : LitMode B) = (j, t) ∧ ph = false
  · rw [if_pos hc]
    simp only [Formula.realize_inf, realize_eqTupF, realize_canonF]
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃⟩
      exact ⟨hc, h₁, h₂, h₃⟩
    · rintro ⟨-, h₁, h₂, h₃⟩
      exact ⟨⟨h₁, h₂⟩, h₃⟩
  · rw [if_neg hc]
    constructor
    · exact fun h => h.elim
    · rintro ⟨h, -⟩
      exact absurd h hc

omit [Finite A] [Nonempty A] in
/-- A walk node is accepting exactly when its current literal is its start
again, with the flag up. -/
theorem isTgt_inl_iff {i j : B.ι} {s t ph : Bool}
    {x : Fin (clauseDim B k + clauseDim B k) → A} :
    (spec prog).IsTgt (Sum.inl ((i, s), (j, t), ph), x) ↔
      (((i, s) : LitMode B) = (j, t) ∧ ph = true) ∧
        ((fun m => x (sndHalf (clauseDim B k) m)) =
          fun m => x (fstHalf (clauseDim B k) m)) := by
  classical
  change (tgtF prog (Sum.inl ((i, s), (j, t), ph))).Realize x ↔ _
  rw [tgtF]
  by_cases hc : ((i, s) : LitMode B) = (j, t) ∧ ph = true
  · rw [if_pos hc]
    rw [realize_eqTupF]
    exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩
  · rw [if_neg hc]
    constructor
    · exact fun h => h.elim
    · rintro ⟨h, -⟩
      exact absurd h hc

omit [Finite A] in
/-- The goal-reporting mode is a starting mode exactly when a goal clause
fires. -/
theorem isSrc_inr_iff {x : Fin (clauseDim B k + clauseDim B k) → A} :
    (spec prog).IsSrc (Sum.inr (), x) ↔ KromImpl.GoalFires prog A :=
  realize_goalF prog

omit [Finite A] in
/-- The goal-reporting mode is accepting exactly when a goal clause fires. -/
theorem isTgt_inr_iff {x : Fin (clauseDim B k + clauseDim B k) → A} :
    (spec prog).IsTgt (Sum.inr (), x) ↔ KromImpl.GoalFires prog A :=
  realize_goalF prog

end Endpoints

/-! ### Correctness -/

section Correctness

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- **Correctness**: the specification accepts exactly when the program is
unsatisfiable – either a goal clause fires, in the reporting mode, or some
literal of the implication graph reaches its own negation and back, which the
cycle-witnessing walk sees as a walk from `(p, p, false)` to `(p, p, true)`. -/
theorem accepts_iff_not_exists_holds :
    (spec prog).Accepts A ↔ ¬∃ ρ : B.Assignment A, prog.Holds ρ := by
  classical
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  have key : (¬∃ ρ : B.Assignment A, prog.Holds ρ) ↔
      (KromImpl.GoalFires prog A ∨
        ∃ p : TwoCnf.Lit (KromImpl.KromAtom B A),
          TwoCnf.Reach (KromImpl.clauseRel prog) p (TwoCnf.neg p) ∧
            TwoCnf.Reach (KromImpl.clauseRel prog) (TwoCnf.neg p) p) := by
    rw [KromImpl.exists_holds_iff, not_and_or, not_not, not_forall]
    simp only [not_not]
  rw [key]
  constructor
  · rintro ⟨⟨um, ux⟩, v, hu, hv, huv⟩
    cases um with
    | inr u => exact Or.inl ((isSrc_inr_iff prog).mp hu)
    | inl p =>
      obtain ⟨q, y, rfl, hcarry⟩ := carryReach_of_reach prog huv
      obtain ⟨⟨i, s⟩, ⟨j, t⟩, ph⟩ := p
      obtain ⟨⟨i', s'⟩, ⟨j', t'⟩, ph'⟩ := q
      obtain ⟨⟨hij, rfl⟩, hhalf, -, -⟩ := (isSrc_inl_iff prog).mp hu
      obtain ⟨⟨hij', rfl⟩, hhalf'⟩ := (isTgt_inl_iff prog).mp hv
      injection hij with hi hs
      injection hij' with hi' hs'
      subst hi; subst hs; subst hi'; subst hs'
      -- both endpoints decode to a node whose two literals agree
      have hdec : decodeNode (((i, s), (i, s), false) : Walk B) ux =
          (litAt i s (fun m => ux (fstHalf (clauseDim B k) m)),
            litAt i s (fun m => ux (fstHalf (clauseDim B k) m)), false) := by
        rw [decodeNode, hhalf]
      have hdec' : decodeNode (((i', s'), (i', s'), true) : Walk B) y =
          (litAt i' s' (fun m => y (fstHalf (clauseDim B k) m)),
            litAt i' s' (fun m => y (fstHalf (clauseDim B k) m)), true) := by
        rw [decodeNode, hhalf']
      -- the start literal is the same at both ends
      have hstart : litAt i' s' (fun m => y (fstHalf (clauseDim B k) m)) =
          litAt i s (fun m => ux (fstHalf (clauseDim B k) m)) := by
        have h := TwoCnf.start_of_carryReach hcarry
        rw [hdec, hdec'] at h
        exact h
      rw [hdec, hdec', hstart] at hcarry
      exact Or.inr ⟨_, (TwoCnf.carryReach_iff _).mp hcarry⟩
  · rintro (hgoal | ⟨p, hbad⟩)
    · exact ⟨(Sum.inr (), fun _ => a₀), (Sum.inr (), fun _ => a₀),
        (isSrc_inr_iff prog).mpr hgoal, (isTgt_inr_iff prog).mpr hgoal,
        Relation.ReflTransGen.refl⟩
    · have hcarry := (TwoCnf.carryReach_iff (Cl := KromImpl.clauseRel prog) p).mpr hbad
      have hcan : ∀ n : TwoCnf.CarryNode (KromImpl.KromAtom B A),
          n.1 = p → n.2.1 = p →
            ((fun m => tupleOf a₀ n (sndHalf (clauseDim B k) m)) =
              fun m => tupleOf a₀ n (fstHalf (clauseDim B k) m)) ∧
            Canon (B.arity p.1.1) (fun m => tupleOf a₀ n (fstHalf (clauseDim B k) m)) ∧
            Canon (B.arity p.1.1) (fun m => tupleOf a₀ n (sndHalf (clauseDim B k) m)) := by
        intro n h₁ h₂
        have e₁ : (fun m => tupleOf a₀ n (fstHalf (clauseDim B k) m)) = pad a₀ p.1.2 := by
          rw [← h₁]
          exact funext fun m => tupleOf_fstHalf a₀ n m
        have e₂ : (fun m => tupleOf a₀ n (sndHalf (clauseDim B k) m)) = pad a₀ p.1.2 := by
          rw [← h₂]
          exact funext fun m => tupleOf_sndHalf a₀ n m
        rw [e₁, e₂]
        exact ⟨rfl, canon_pad ha₀ _ _, canon_pad ha₀ _ _⟩
      obtain ⟨he₁, he₂, he₃⟩ := hcan (p, p, false) rfl rfl
      obtain ⟨hf₁, -, -⟩ := hcan (p, p, true) rfl rfl
      exact ⟨(Sum.inl (modeOf ((p, p, false) : TwoCnf.CarryNode (KromImpl.KromAtom B A))),
          tupleOf a₀ (p, p, false)),
        (Sum.inl (modeOf ((p, p, true) : TwoCnf.CarryNode (KromImpl.KromAtom B A))),
          tupleOf a₀ (p, p, true)),
        (isSrc_inl_iff prog).mpr ⟨⟨rfl, rfl⟩, he₁, he₂, he₃⟩,
        (isTgt_inl_iff prog).mpr ⟨⟨rfl, rfl⟩, hf₁⟩,
        reach_of_carryReach prog ha₀ hcarry⟩

end Correctness

end Spec

end KromTC

open KromTC in
/-- **The complement of an SO-Krom definable problem is FO(TC) definable**: a
Krom program instantiated in a structure is a 2-CNF on the atoms of its block,
so it is unsatisfiable exactly when a goal clause fires or some literal reaches
its own negation and back, and the second condition is a single walk of the
cycle-witnessing graph – whose nodes are a pair of literals and a flag, i.e. a
mode and two canonically padded tuples. Together with
`DescriptiveComplexity.SigmaSOKromDefinable.compl_of_tcDefinable` this gives
`co-NL(Krom) = NL(TC)`; it is upgraded to `NL = coNL` by Immerman–Szelepcsényi
(`DescriptiveComplexity.NL_eq_coNL`). -/
theorem TCDefinable.compl_of_sigmaSOKromDefinable {L : Language.{0, 0}}
    [L.IsRelational] {P : DecisionProblem L} (h : SigmaSOKromDefinable P) : TCDefinable Pᶜ := by
  obtain ⟨B, k, prog, hprog⟩ := h
  refine ⟨spec prog, ?_⟩
  intro A _ _ _ _
  exact (not_congr (hprog A)).trans (accepts_iff_not_exists_holds prog).symm

/-- **The two translations compose**: a problem is SO-Krom definable exactly
when its complement is FO(TC) definable, `co-NL(Krom) = NL(TC)`. -/
theorem sigmaSOKromDefinable_iff_tcDefinable_compl {L : Language.{0, 0}}
    [L.IsRelational] (P : DecisionProblem L) : SigmaSOKromDefinable P ↔ TCDefinable Pᶜ := by
  refine ⟨TCDefinable.compl_of_sigmaSOKromDefinable, fun h => ?_⟩
  have := SigmaSOKromDefinable.compl_of_tcDefinable h
  rwa [DecisionProblem.compl_compl] at this

/-- **NL is the complements of the FO(TC) definable problems.** -/
theorem mem_NL_iff_tcDefinable_compl {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    P ∈ NL ↔ TCDefinable Pᶜ :=
  (mem_NL_iff P).trans (sigmaSOKromDefinable_iff_tcDefinable_compl P)

end DescriptiveComplexity
