/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.SuccinctReach.Membership
import DescriptiveComplexity.Problems.SuccinctReach.Double
import DescriptiveComplexity.Problems.Sat.TseitinFormulas

/-!
# SUCCINCT-REACH is PSPACE-hard

The hardness half: every SO(TC) definable problem admits an ordered first-order
reduction to SUCCINCT-REACH (`DescriptiveComplexity.succinctReach_hard_of_sotcDefinable`).
Since `DescriptiveComplexity.PSPACE` is *defined* as SO(TC) definability, together
with `DescriptiveComplexity.succinctReach_mem_PSPACE` this makes SUCCINCT-REACH
PSPACE-complete.

## The discharge, and why it is three Tseitin encodings sharing one block

A `DescriptiveComplexity.SOTCSpec` is a block `B` and three first-order sentences:
a transition sentence over two copies of `B` and two endpoint sentences over
one. The interpreted SUCCINCT-REACH instance is, group by group, the Tseitin
encoding ([Tseitin 1968][tseitin1968complexity]) of those sentences – the very
construction that discharges `∃SO` into SAT
(`DescriptiveComplexity.sat_hard_of_sigmaSODefinable`), reused wholesale through its
semantic interface `DescriptiveComplexity.Tseitin.satCond_iff_gates`.

The one thing that is *not* three independent encodings is the block: all three
are taken over the **doubled** block `B.double`
(`DescriptiveComplexity.Problems.SuccinctReach.Double`), the endpoint sentences being
renamed into its first copy. That is forced, and it is the heart of the
construction: the propositional variables standing for the atoms of the block
must be *the same elements* in the three clause groups, since they are exactly
the state variables the walk carries. So

* an atom `(i, x̄)` of the first copy is a state variable, marked by `stateVar`;
* the atom `(i, x̄)` of the second copy is its next-state copy, paired to it by
  `next`;
* the gates of each encoding are auxiliary variables, private to their group.

A state of the interpreted transition system is then a set of atoms of the
first copy, i.e. an assignment of `B` – the state of the SO(TC) walk – and the
transition clauses hold of a valuation exactly when the transition sentence
holds of the pair it reads and writes. The correspondence between the two walks
is a bijection at every step, with no initialization or finalization steps to
peel off, which is why the endpoint conditions are kept as two extra clause
groups rather than folded into the transition.

## Junk

Only the *canonically padded* tuples carry meaning, as in the SAT discharge:
tuples of length `DescriptiveComplexity.srDim` are padded with minimal elements of
the order, and a clause mentions no variable at a non-canonical tuple. But
`stateVar` and `next` are declared at *every* tuple, canonical or not. Junk
state variables are then free-running copies whose values no clause constrains
and no reading of a state ever looks at (`DescriptiveComplexity.srPredOf` reads the
canonical padding only), so they cost nothing and save the canonicity guards.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure Tseitin

namespace SuccinctReachHard

variable {L : Language.{0, 0}} (B : SOBlock)
  (stepS : (((L.sum Language.order).sum B.lang).sum B.lang).Sentence)
  (srcS tgtS : ((L.sum Language.order).sum B.lang).Sentence)

/-! ### The three kernels, over the doubled block -/

/-- The transition sentence, read over the doubled block. -/
noncomputable def stepK : ((L.sum Language.order).sum B.double.lang).Sentence :=
  (blockPairLHom B).onSentence stepS

/-- The source sentence, read over the doubled block (first copy only). -/
noncomputable def srcK : ((L.sum Language.order).sum B.double.lang).Sentence :=
  (blockFstLHom B).onSentence srcS

/-- The target sentence, read over the doubled block (first copy only). -/
noncomputable def tgtK : ((L.sum Language.order).sum B.double.lang).Sentence :=
  (blockFstLHom B).onSentence tgtS

/-- The dimension of the interpretation: large enough for every context tuple
of the three kernels and every argument tuple of a block variable. -/
noncomputable def srDim : ℕ :=
  max (max (maxCtx (stepK B stepS)) (max (maxCtx (srcK B srcS)) (maxCtx (tgtK B tgtS))))
    (blockArityBound B.double)

theorem ctx_step : maxCtx (stepK B stepS) ≤ srDim B stepS srcS tgtS :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem ctx_src : maxCtx (srcK B srcS) ≤ srDim B stepS srcS tgtS :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)

theorem ctx_tgt : maxCtx (tgtK B tgtS) ≤ srDim B stepS srcS tgtS :=
  ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)

theorem arity_le_srDim (i : B.double.ι) :
    B.double.arity i ≤ srDim B stepS srcS tgtS :=
  (arity_le_blockArityBound B.double i).trans (le_max_right _ _)

/-! ### Tags -/

/-- Subformula positions of the transition kernel. -/
abbrev StepNode : Type := Σ m, NodeAt (stepK B stepS) m

/-- Subformula positions of the source kernel. -/
abbrev SrcNode : Type := Σ m, NodeAt (srcK B srcS) m

/-- Subformula positions of the target kernel. -/
abbrev TgtNode : Type := Σ m, NodeAt (tgtK B tgtS) m

/-- The tags of the interpretation: the clauses of the three Tseitin
encodings (one per position and kind, plus the top unit clause of each
group), then the propositional variables – the shared atoms of the doubled
block, and the gates of each group. -/
abbrev SRTag : Type :=
  (((StepNode B stepS × Fin 3) ⊕ Unit) ⊕
      (((SrcNode B srcS × Fin 3) ⊕ Unit) ⊕ ((TgtNode B tgtS × Fin 3) ⊕ Unit))) ⊕
    (B.double.ι ⊕ (StepNode B stepS ⊕ (SrcNode B srcS ⊕ TgtNode B tgtS)))

instance : Nonempty (SRTag B stepS srcS tgtS) :=
  ⟨Sum.inl (Sum.inl (Sum.inr ()))⟩

variable {B stepS srcS tgtS}

/-- The clause of the transition group at a position and kind. -/
abbrev tagStepCl (σp : StepNode B stepS) (k : Fin 3) : SRTag B stepS srcS tgtS :=
  Sum.inl (Sum.inl (Sum.inl (σp, k)))

/-- The top unit clause of the transition group. -/
abbrev tagStepTop : SRTag B stepS srcS tgtS := Sum.inl (Sum.inl (Sum.inr ()))

/-- The clause of the source group at a position and kind. -/
abbrev tagSrcCl (σp : SrcNode B srcS) (k : Fin 3) : SRTag B stepS srcS tgtS :=
  Sum.inl (Sum.inr (Sum.inl (Sum.inl (σp, k))))

/-- The top unit clause of the source group. -/
abbrev tagSrcTop : SRTag B stepS srcS tgtS := Sum.inl (Sum.inr (Sum.inl (Sum.inr ())))

/-- The clause of the target group at a position and kind. -/
abbrev tagTgtCl (σp : TgtNode B tgtS) (k : Fin 3) : SRTag B stepS srcS tgtS :=
  Sum.inl (Sum.inr (Sum.inr (Sum.inl (σp, k))))

/-- The top unit clause of the target group. -/
abbrev tagTgtTop : SRTag B stepS srcS tgtS := Sum.inl (Sum.inr (Sum.inr (Sum.inr ())))

/-- The propositional variable of an atom of the doubled block: a state
variable for the first copy, its next-state copy for the second. -/
abbrev tagAtom (i : B.double.ι) : SRTag B stepS srcS tgtS := Sum.inr (Sum.inl i)

/-- A gate variable of the transition group. -/
abbrev tagStepGate (σp : StepNode B stepS) : SRTag B stepS srcS tgtS :=
  Sum.inr (Sum.inr (Sum.inl σp))

/-- A gate variable of the source group. -/
abbrev tagSrcGate (σp : SrcNode B srcS) : SRTag B stepS srcS tgtS :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl σp)))

/-- A gate variable of the target group. -/
abbrev tagTgtGate (σp : TgtNode B tgtS) : SRTag B stepS srcS tgtS :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr σp)))

/-- The Tseitin variable tags of the transition group, as tags of the
interpretation. -/
def stepVar : (B.double.ι ⊕ StepNode B stepS) → SRTag B stepS srcS tgtS :=
  Sum.elim tagAtom tagStepGate

/-- The Tseitin variable tags of the source group, as tags. -/
def srcVar : (B.double.ι ⊕ SrcNode B srcS) → SRTag B stepS srcS tgtS :=
  Sum.elim tagAtom tagSrcGate

/-- The Tseitin variable tags of the target group, as tags. -/
def tgtVar : (B.double.ι ⊕ TgtNode B tgtS) → SRTag B stepS srcS tgtS :=
  Sum.elim tagAtom tagTgtGate

variable (B stepS srcS tgtS)

/-! ### The defining formulas -/

/-- The coordinate selector of a unary relation's single argument. -/
abbrev selU : Fin (srDim B stepS srcS tgtS) → Fin 1 × Fin (srDim B stepS srcS tgtS) :=
  fun j => ((0 : Fin 1), j)

/-- The coordinate selector of a binary relation's first argument. -/
abbrev selA : Fin (srDim B stepS srcS tgtS) → Fin 2 × Fin (srDim B stepS srcS tgtS) :=
  fun j => ((0 : Fin 2), j)

/-- The coordinate selector of a binary relation's second argument. -/
abbrev selB : Fin (srDim B stepS srcS tgtS) → Fin 2 × Fin (srDim B stepS srcS tgtS) :=
  fun j => ((1 : Fin 2), j)

/-- Merging the two order symbols the Tseitin builders leave behind: they add
an order to the vocabulary they are given, which here is already ordered. -/
noncomputable abbrev mrg {γ : Type}
    (φ : ((L.sum Language.order).sum Language.order).Formula γ) :
    (L.sum Language.order).Formula γ :=
  (mergeOrdLHom L).onFormula φ

open Classical in
/-- The defining formula of `stepCl`, `srcCl` or `tgtCl`, selected by which
group's clauses it should recognize: the clause-existence formulas of that
group's encoding, plus the canonicity condition of its top unit clause. -/
noncomputable def srClFml (t : SRTag B stepS srcS tgtS) :
    (L.sum Language.order).Formula (Fin 1 × Fin (srDim B stepS srcS tgtS)) :=
  match t with
  | Sum.inl (Sum.inl (Sum.inl (σp, k))) =>
      mrg (isClauseF (stepK B stepS) (ctx_step B stepS srcS tgtS) σp.2 k
        (selU B stepS srcS tgtS))
  | Sum.inl (Sum.inl (Sum.inr _)) => canonF 0 (selU B stepS srcS tgtS)
  | _ => ⊥

open Classical in
/-- The defining formula of `srcCl`. -/
noncomputable def srSrcClFml (t : SRTag B stepS srcS tgtS) :
    (L.sum Language.order).Formula (Fin 1 × Fin (srDim B stepS srcS tgtS)) :=
  match t with
  | Sum.inl (Sum.inr (Sum.inl (Sum.inl (σp, k)))) =>
      mrg (isClauseF (srcK B srcS) (ctx_src B stepS srcS tgtS) σp.2 k
        (selU B stepS srcS tgtS))
  | Sum.inl (Sum.inr (Sum.inl (Sum.inr _))) => canonF 0 (selU B stepS srcS tgtS)
  | _ => ⊥

open Classical in
/-- The defining formula of `tgtCl`. -/
noncomputable def srTgtClFml (t : SRTag B stepS srcS tgtS) :
    (L.sum Language.order).Formula (Fin 1 × Fin (srDim B stepS srcS tgtS)) :=
  match t with
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl (σp, k)))) =>
      mrg (isClauseF (tgtK B tgtS) (ctx_tgt B stepS srcS tgtS) σp.2 k
        (selU B stepS srcS tgtS))
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr _))) => canonF 0 (selU B stepS srcS tgtS)
  | _ => ⊥

/-- The defining formula of `stateVar`: the atoms of the *first* copy of the
doubled block, at every tuple. -/
noncomputable def srStateFml (t : SRTag B stepS srcS tgtS) :
    (L.sum Language.order).Formula (Fin 1 × Fin (srDim B stepS srcS tgtS)) :=
  match t with
  | Sum.inr (Sum.inl (Sum.inl _)) => ⊤
  | _ => ⊥

open Classical in
/-- The defining formula of `next`: the atom of the second copy at the same
relation variable and the same tuple. -/
noncomputable def srNextFml (t₁ t₂ : SRTag B stepS srcS tgtS) :
    (L.sum Language.order).Formula (Fin 2 × Fin (srDim B stepS srcS tgtS)) :=
  match t₁, t₂ with
  | Sum.inr (Sum.inl (Sum.inl i)), Sum.inr (Sum.inl (Sum.inr i')) =>
      if i = i' then eqTupF (selA B stepS srcS tgtS) (selB B stepS srcS tgtS) else ⊥
  | _, _ => ⊥

open Classical in
/-- The literals of a node clause of the transition group: an atom of the
block, or a gate of that group. -/
noncomputable def srLitStep (s : Bool) (σp : StepNode B stepS) (k : Fin 3)
    (tx : SRTag B stepS srcS tgtS) :
    (L.sum Language.order).Formula (Fin 2 × Fin (srDim B stepS srcS tgtS)) :=
  match tx with
  | Sum.inr (Sum.inl i) =>
      mrg (litF s (stepK B stepS) (ctx_step B stepS srcS tgtS) σp.2 k (Sum.inl i)
        (selA B stepS srcS tgtS) (selB B stepS srcS tgtS))
  | Sum.inr (Sum.inr (Sum.inl σq)) =>
      mrg (litF s (stepK B stepS) (ctx_step B stepS srcS tgtS) σp.2 k (Sum.inr σq)
        (selA B stepS srcS tgtS) (selB B stepS srcS tgtS))
  | _ => ⊥

open Classical in
/-- The literal of the top unit clause of the transition group: its root
gate, positively, at fully padded tuples. -/
noncomputable def srLitStepTop (s : Bool) (tx : SRTag B stepS srcS tgtS) :
    (L.sum Language.order).Formula (Fin 2 × Fin (srDim B stepS srcS tgtS)) :=
  match tx with
  | Sum.inr (Sum.inr (Sum.inl σq)) =>
      if isRootB (stepK B stepS) σq.2 && s then
        canonF 0 (selA B stepS srcS tgtS) ⊓ canonF 0 (selB B stepS srcS tgtS)
      else ⊥
  | _ => ⊥

open Classical in
/-- The literals of a node clause of the source group. -/
noncomputable def srLitSrc (s : Bool) (σp : SrcNode B srcS) (k : Fin 3)
    (tx : SRTag B stepS srcS tgtS) :
    (L.sum Language.order).Formula (Fin 2 × Fin (srDim B stepS srcS tgtS)) :=
  match tx with
  | Sum.inr (Sum.inl i) =>
      mrg (litF s (srcK B srcS) (ctx_src B stepS srcS tgtS) σp.2 k (Sum.inl i)
        (selA B stepS srcS tgtS) (selB B stepS srcS tgtS))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl σq))) =>
      mrg (litF s (srcK B srcS) (ctx_src B stepS srcS tgtS) σp.2 k (Sum.inr σq)
        (selA B stepS srcS tgtS) (selB B stepS srcS tgtS))
  | _ => ⊥

open Classical in
/-- The literal of the top unit clause of the source group. -/
noncomputable def srLitSrcTop (s : Bool) (tx : SRTag B stepS srcS tgtS) :
    (L.sum Language.order).Formula (Fin 2 × Fin (srDim B stepS srcS tgtS)) :=
  match tx with
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl σq))) =>
      if isRootB (srcK B srcS) σq.2 && s then
        canonF 0 (selA B stepS srcS tgtS) ⊓ canonF 0 (selB B stepS srcS tgtS)
      else ⊥
  | _ => ⊥

open Classical in
/-- The literals of a node clause of the target group. -/
noncomputable def srLitTgt (s : Bool) (σp : TgtNode B tgtS) (k : Fin 3)
    (tx : SRTag B stepS srcS tgtS) :
    (L.sum Language.order).Formula (Fin 2 × Fin (srDim B stepS srcS tgtS)) :=
  match tx with
  | Sum.inr (Sum.inl i) =>
      mrg (litF s (tgtK B tgtS) (ctx_tgt B stepS srcS tgtS) σp.2 k (Sum.inl i)
        (selA B stepS srcS tgtS) (selB B stepS srcS tgtS))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr σq))) =>
      mrg (litF s (tgtK B tgtS) (ctx_tgt B stepS srcS tgtS) σp.2 k (Sum.inr σq)
        (selA B stepS srcS tgtS) (selB B stepS srcS tgtS))
  | _ => ⊥

open Classical in
/-- The literal of the top unit clause of the target group. -/
noncomputable def srLitTgtTop (s : Bool) (tx : SRTag B stepS srcS tgtS) :
    (L.sum Language.order).Formula (Fin 2 × Fin (srDim B stepS srcS tgtS)) :=
  match tx with
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr σq))) =>
      if isRootB (tgtK B tgtS) σq.2 && s then
        canonF 0 (selA B stepS srcS tgtS) ⊓ canonF 0 (selB B stepS srcS tgtS)
      else ⊥
  | _ => ⊥

/-- The defining formula of `posIn` (`s = true`) and `negIn` (`s = false`),
dispatching on which group's clause the first argument is. -/
noncomputable def srLitFml (s : Bool) (tc tx : SRTag B stepS srcS tgtS) :
    (L.sum Language.order).Formula (Fin 2 × Fin (srDim B stepS srcS tgtS)) :=
  match tc with
  | Sum.inl (Sum.inl (Sum.inl (σp, k))) => srLitStep B stepS srcS tgtS s σp k tx
  | Sum.inl (Sum.inl (Sum.inr _)) => srLitStepTop B stepS srcS tgtS s tx
  | Sum.inl (Sum.inr (Sum.inl (Sum.inl (σp, k)))) => srLitSrc B stepS srcS tgtS s σp k tx
  | Sum.inl (Sum.inr (Sum.inl (Sum.inr _))) => srLitSrcTop B stepS srcS tgtS s tx
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl (σp, k)))) => srLitTgt B stepS srcS tgtS s σp k tx
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr _))) => srLitTgtTop B stepS srcS tgtS s tx
  | Sum.inr _ => ⊥

/-- **The interpretation**: the SUCCINCT-REACH instance of an SO(TC)
specification, defined inside the ordered input structure. -/
noncomputable def srInterp :
    FOInterpretation (L.sum Language.order) Language.transSys (SRTag B stepS srcS tgtS)
      (srDim B stepS srcS tgtS) where
  relFormula {_n} R :=
    match R with
    | .stateVar => fun t => srStateFml B stepS srcS tgtS (t 0)
    | .next => fun t => srNextFml B stepS srcS tgtS (t 0) (t 1)
    | .stepCl => fun t => srClFml B stepS srcS tgtS (t 0)
    | .srcCl => fun t => srSrcClFml B stepS srcS tgtS (t 0)
    | .tgtCl => fun t => srTgtClFml B stepS srcS tgtS (t 0)
    | .posIn => fun t => srLitFml B stepS srcS tgtS true (t 0) (t 1)
    | .negIn => fun t => srLitFml B stepS srcS tgtS false (t 0) (t 1)


/-! ### Characterization of the interpreted relations

Each relation of the interpreted instance is characterized by a semantic
counterpart of its defining formula, matching on the tags exactly as the
formula does – the pattern of `DescriptiveComplexity.TseitinLitSem`. -/

section Characterizations

variable {B stepS srcS tgtS} {A : Type} [L.Structure A] [LinearOrder A]

/-- Semantic counterpart of `DescriptiveComplexity.SuccinctReachHard.srStateFml`. -/
def srStateSem (t : SRTag B stepS srcS tgtS) : Prop :=
  match t with
  | Sum.inr (Sum.inl (Sum.inl _)) => True
  | _ => False

/-- Semantic counterpart of `DescriptiveComplexity.SuccinctReachHard.srNextFml`. -/
def srNextSem (t₁ t₂ : SRTag B stepS srcS tgtS)
    (u x : Fin (srDim B stepS srcS tgtS) → A) : Prop :=
  match t₁, t₂ with
  | Sum.inr (Sum.inl (Sum.inl i)), Sum.inr (Sum.inl (Sum.inr i')) => i = i' ∧ x = u
  | _, _ => False

/-- Semantic counterpart of `DescriptiveComplexity.SuccinctReachHard.srClFml`. -/
def srClSem (t : SRTag B stepS srcS tgtS)
    (u : Fin (srDim B stepS srcS tgtS) → A) : Prop :=
  match t with
  | Sum.inl (Sum.inl (Sum.inl (σp, k))) =>
      IsClauseSem (stepK B stepS) (ctx_step B stepS srcS tgtS) σp.2 k u
  | Sum.inl (Sum.inl (Sum.inr _)) => Canon 0 u
  | _ => False

/-- Semantic counterpart of `DescriptiveComplexity.SuccinctReachHard.srSrcClFml`. -/
def srSrcClSem (t : SRTag B stepS srcS tgtS)
    (u : Fin (srDim B stepS srcS tgtS) → A) : Prop :=
  match t with
  | Sum.inl (Sum.inr (Sum.inl (Sum.inl (σp, k)))) =>
      IsClauseSem (srcK B srcS) (ctx_src B stepS srcS tgtS) σp.2 k u
  | Sum.inl (Sum.inr (Sum.inl (Sum.inr _))) => Canon 0 u
  | _ => False

/-- Semantic counterpart of `DescriptiveComplexity.SuccinctReachHard.srTgtClFml`. -/
def srTgtClSem (t : SRTag B stepS srcS tgtS)
    (u : Fin (srDim B stepS srcS tgtS) → A) : Prop :=
  match t with
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl (σp, k)))) =>
      IsClauseSem (tgtK B tgtS) (ctx_tgt B stepS srcS tgtS) σp.2 k u
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr _))) => Canon 0 u
  | _ => False

/-- Semantic counterpart of `DescriptiveComplexity.SuccinctReachHard.srLitStep`. -/
def srLitStepSem (s : Bool) (σp : StepNode B stepS) (k : Fin 3)
    (tx : SRTag B stepS srcS tgtS) (u x : Fin (srDim B stepS srcS tgtS) → A) : Prop :=
  match tx with
  | Sum.inr (Sum.inl i) => 
      LitSem s (stepK B stepS) (ctx_step B stepS srcS tgtS) σp.2 k u (Sum.inl i) x
  | Sum.inr (Sum.inr (Sum.inl σq)) => 
      LitSem s (stepK B stepS) (ctx_step B stepS srcS tgtS) σp.2 k u (Sum.inr σq) x
  | _ => False

/-- Semantic counterpart of `DescriptiveComplexity.SuccinctReachHard.srLitStepTop`. -/
def srLitStepTopSem (s : Bool) (tx : SRTag B stepS srcS tgtS)
    (u x : Fin (srDim B stepS srcS tgtS) → A) : Prop :=
  match tx with
  | Sum.inr (Sum.inr (Sum.inl σq)) =>
      s = true ∧ σq = ⟨0, rootAt (stepK B stepS)⟩ ∧ Canon 0 u ∧ Canon 0 x
  | _ => False

/-- Semantic counterpart of `DescriptiveComplexity.SuccinctReachHard.srLitSrc`. -/
def srLitSrcSem (s : Bool) (σp : SrcNode B srcS) (k : Fin 3)
    (tx : SRTag B stepS srcS tgtS) (u x : Fin (srDim B stepS srcS tgtS) → A) : Prop :=
  match tx with
  | Sum.inr (Sum.inl i) => LitSem s (srcK B srcS) (ctx_src B stepS srcS tgtS) σp.2 k u (Sum.inl i) x
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl σq))) => 
      LitSem s (srcK B srcS) (ctx_src B stepS srcS tgtS) σp.2 k u (Sum.inr σq) x
  | _ => False

/-- Semantic counterpart of `DescriptiveComplexity.SuccinctReachHard.srLitSrcTop`. -/
def srLitSrcTopSem (s : Bool) (tx : SRTag B stepS srcS tgtS)
    (u x : Fin (srDim B stepS srcS tgtS) → A) : Prop :=
  match tx with
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl σq))) =>
      s = true ∧ σq = ⟨0, rootAt (srcK B srcS)⟩ ∧ Canon 0 u ∧ Canon 0 x
  | _ => False

/-- Semantic counterpart of `DescriptiveComplexity.SuccinctReachHard.srLitTgt`. -/
def srLitTgtSem (s : Bool) (σp : TgtNode B tgtS) (k : Fin 3)
    (tx : SRTag B stepS srcS tgtS) (u x : Fin (srDim B stepS srcS tgtS) → A) : Prop :=
  match tx with
  | Sum.inr (Sum.inl i) => LitSem s (tgtK B tgtS) (ctx_tgt B stepS srcS tgtS) σp.2 k u (Sum.inl i) x
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr σq))) => 
      LitSem s (tgtK B tgtS) (ctx_tgt B stepS srcS tgtS) σp.2 k u (Sum.inr σq) x
  | _ => False

/-- Semantic counterpart of `DescriptiveComplexity.SuccinctReachHard.srLitTgtTop`. -/
def srLitTgtTopSem (s : Bool) (tx : SRTag B stepS srcS tgtS)
    (u x : Fin (srDim B stepS srcS tgtS) → A) : Prop :=
  match tx with
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr σq))) =>
      s = true ∧ σq = ⟨0, rootAt (tgtK B tgtS)⟩ ∧ Canon 0 u ∧ Canon 0 x
  | _ => False

/-- Semantic counterpart of `DescriptiveComplexity.SuccinctReachHard.srLitFml`. -/
def srLitSem (s : Bool) (tc tx : SRTag B stepS srcS tgtS)
    (u x : Fin (srDim B stepS srcS tgtS) → A) : Prop :=
  match tc with
  | Sum.inl (Sum.inl (Sum.inl (σp, k))) => srLitStepSem s σp k tx u x
  | Sum.inl (Sum.inl (Sum.inr _)) => srLitStepTopSem s tx u x
  | Sum.inl (Sum.inr (Sum.inl (Sum.inl (σp, k)))) => srLitSrcSem s σp k tx u x
  | Sum.inl (Sum.inr (Sum.inl (Sum.inr _))) => srLitSrcTopSem s tx u x
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl (σp, k)))) => srLitTgtSem s σp k tx u x
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr _))) => srLitTgtTopSem s tx u x
  | Sum.inr _ => False

variable (B stepS srcS tgtS)

/-- The realization of a top-clause literal formula, shared by the three
groups: the group's root variable, at fully padded tuples, positively. -/
private theorem realize_topLit {L' : Language.{0, 0}} {n : ℕ}
    (f : L'.BoundedFormula Empty n) (s : Bool) (σq : Σ m, NodeAt f m)
    (v : Fin 2 × Fin (srDim B stepS srcS tgtS) → A) :
    ((if isRootB f σq.2 && s then
        canonF (L := L) 0 (selA B stepS srcS tgtS) ⊓
          canonF (L := L) 0 (selB B stepS srcS tgtS)
      else ⊥).Realize v) ↔
      (s = true ∧ σq = ⟨n, rootAt f⟩ ∧ Canon 0 (fun j => v (selA B stepS srcS tgtS j)) ∧
        Canon 0 fun j => v (selB B stepS srcS tgtS j)) := by
  split_ifs with hb
  · rw [Formula.realize_inf, realize_canonF, realize_canonF]
    obtain ⟨hroot, rfl⟩ : isRootB f σq.2 = true ∧ s = true := by simpa using hb
    have hσ : σq = ⟨n, rootAt f⟩ := (Sigma.eta σq) ▸ (isRootB_iff f σq.2).mp hroot
    exact ⟨fun h => ⟨rfl, hσ, h.1, h.2⟩, fun h => ⟨h.2.2.1, h.2.2.2⟩⟩
  · rw [Formula.realize_bot]
    refine iff_of_false id ?_
    rintro ⟨rfl, rfl, -, -⟩
    refine hb ?_
    rw [Bool.and_true]
    exact (isRootB_iff f (rootAt f)).mpr rfl

variable {B stepS srcS tgtS}

theorem sr_stateVar_iff (t : SRTag B stepS srcS tgtS)
    (u : Fin (srDim B stepS srcS tgtS) → A) :
    RelMap (M := (srInterp B stepS srcS tgtS).Map A) tsStateVar ![(t, u)] ↔
      srStateSem t := by
  rw [FOInterpretation.relMap_map]
  match t with
  | Sum.inr (Sum.inl (Sum.inl i)) => exact Formula.realize_top
  | Sum.inr (Sum.inl (Sum.inr i)) => exact Formula.realize_bot
  | Sum.inr (Sum.inr _) => exact Formula.realize_bot
  | Sum.inl _ => exact Formula.realize_bot

theorem sr_next_iff (t₁ t₂ : SRTag B stepS srcS tgtS)
    (u x : Fin (srDim B stepS srcS tgtS) → A) :
    RelMap (M := (srInterp B stepS srcS tgtS).Map A) tsNext ![(t₁, u), (t₂, x)] ↔
      srNextSem t₁ t₂ u x := by
  classical
  rw [FOInterpretation.relMap_map]
  match t₁, t₂ with
  | Sum.inr (Sum.inl (Sum.inl i)), Sum.inr (Sum.inl (Sum.inr i')) =>
      change ((if i = i' then eqTupF (selA B stepS srcS tgtS) (selB B stepS srcS tgtS)
        else ⊥).Realize _) ↔ _
      split_ifs with hi
      · rw [realize_eqTupF]
        exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩
      · rw [Formula.realize_bot]
        exact iff_of_false id fun h => hi h.1
  | Sum.inr (Sum.inl (Sum.inl i)), Sum.inr (Sum.inl (Sum.inl i')) => exact Formula.realize_bot
  | Sum.inr (Sum.inl (Sum.inl i)), Sum.inr (Sum.inr _) => exact Formula.realize_bot
  | Sum.inr (Sum.inl (Sum.inl i)), Sum.inl _ => exact Formula.realize_bot
  | Sum.inr (Sum.inl (Sum.inr i)), _ => exact Formula.realize_bot
  | Sum.inr (Sum.inr _), _ => exact Formula.realize_bot
  | Sum.inl _, _ => exact Formula.realize_bot

theorem realize_srLitStep (s : Bool) (σp : StepNode B stepS) (k : Fin 3)
    (tx : SRTag B stepS srcS tgtS) (v : Fin 2 × Fin (srDim B stepS srcS tgtS) → A) :
    (srLitStep B stepS srcS tgtS s σp k tx).Realize v ↔
      srLitStepSem s σp k tx (fun j => v (selA B stepS srcS tgtS j))
        (fun j => v (selB B stepS srcS tgtS j)) := by
  match tx with
  | Sum.inr (Sum.inl i) =>
      exact (realize_mergeOrdLHom _ _).trans (realize_litF s _ _ _ _ _ _ _)
  | Sum.inr (Sum.inr (Sum.inl σq)) =>
      exact (realize_mergeOrdLHom _ _).trans (realize_litF s _ _ _ _ _ _ _)
  | Sum.inr (Sum.inr (Sum.inr _)) => exact Formula.realize_bot
  | Sum.inl _ => exact Formula.realize_bot

theorem realize_srLitSrc (s : Bool) (σp : SrcNode B srcS) (k : Fin 3)
    (tx : SRTag B stepS srcS tgtS) (v : Fin 2 × Fin (srDim B stepS srcS tgtS) → A) :
    (srLitSrc B stepS srcS tgtS s σp k tx).Realize v ↔
      srLitSrcSem s σp k tx (fun j => v (selA B stepS srcS tgtS j))
        (fun j => v (selB B stepS srcS tgtS j)) := by
  match tx with
  | Sum.inr (Sum.inl i) =>
      exact (realize_mergeOrdLHom _ _).trans (realize_litF s _ _ _ _ _ _ _)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl σq))) =>
      exact (realize_mergeOrdLHom _ _).trans (realize_litF s _ _ _ _ _ _ _)
  | Sum.inr (Sum.inr (Sum.inl _)) => exact Formula.realize_bot
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => exact Formula.realize_bot
  | Sum.inl _ => exact Formula.realize_bot

theorem realize_srLitTgt (s : Bool) (σp : TgtNode B tgtS) (k : Fin 3)
    (tx : SRTag B stepS srcS tgtS) (v : Fin 2 × Fin (srDim B stepS srcS tgtS) → A) :
    (srLitTgt B stepS srcS tgtS s σp k tx).Realize v ↔
      srLitTgtSem s σp k tx (fun j => v (selA B stepS srcS tgtS j))
        (fun j => v (selB B stepS srcS tgtS j)) := by
  match tx with
  | Sum.inr (Sum.inl i) =>
      exact (realize_mergeOrdLHom _ _).trans (realize_litF s _ _ _ _ _ _ _)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr σq))) =>
      exact (realize_mergeOrdLHom _ _).trans (realize_litF s _ _ _ _ _ _ _)
  | Sum.inr (Sum.inr (Sum.inl _)) => exact Formula.realize_bot
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => exact Formula.realize_bot
  | Sum.inl _ => exact Formula.realize_bot

theorem realize_srLitStepTop (s : Bool) (tx : SRTag B stepS srcS tgtS)
    (v : Fin 2 × Fin (srDim B stepS srcS tgtS) → A) :
    (srLitStepTop B stepS srcS tgtS s tx).Realize v ↔
      srLitStepTopSem s tx (fun j => v (selA B stepS srcS tgtS j))
        (fun j => v (selB B stepS srcS tgtS j)) := by
  match tx with
  | Sum.inr (Sum.inr (Sum.inl σq)) =>
      exact realize_topLit (f := stepK B stepS) (s := s) (σq := σq) (v := v)
  | Sum.inr (Sum.inr (Sum.inr _)) => exact Formula.realize_bot
  | Sum.inr (Sum.inl _) => exact Formula.realize_bot
  | Sum.inl _ => exact Formula.realize_bot

theorem realize_srLitSrcTop (s : Bool) (tx : SRTag B stepS srcS tgtS)
    (v : Fin 2 × Fin (srDim B stepS srcS tgtS) → A) :
    (srLitSrcTop B stepS srcS tgtS s tx).Realize v ↔
      srLitSrcTopSem s tx (fun j => v (selA B stepS srcS tgtS j))
        (fun j => v (selB B stepS srcS tgtS j)) := by
  match tx with
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl σq))) =>
      exact realize_topLit (f := srcK B srcS) (s := s) (σq := σq) (v := v)
  | Sum.inr (Sum.inr (Sum.inl _)) => exact Formula.realize_bot
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => exact Formula.realize_bot
  | Sum.inr (Sum.inl _) => exact Formula.realize_bot
  | Sum.inl _ => exact Formula.realize_bot

theorem realize_srLitTgtTop (s : Bool) (tx : SRTag B stepS srcS tgtS)
    (v : Fin 2 × Fin (srDim B stepS srcS tgtS) → A) :
    (srLitTgtTop B stepS srcS tgtS s tx).Realize v ↔
      srLitTgtTopSem s tx (fun j => v (selA B stepS srcS tgtS j))
        (fun j => v (selB B stepS srcS tgtS j)) := by
  match tx with
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr σq))) =>
      exact realize_topLit (f := tgtK B tgtS) (s := s) (σq := σq) (v := v)
  | Sum.inr (Sum.inr (Sum.inl _)) => exact Formula.realize_bot
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => exact Formula.realize_bot
  | Sum.inr (Sum.inl _) => exact Formula.realize_bot
  | Sum.inl _ => exact Formula.realize_bot

theorem sr_stepCl_iff (t : SRTag B stepS srcS tgtS) (u : Fin (srDim B stepS srcS tgtS) → A) :
    RelMap (M := (srInterp B stepS srcS tgtS).Map A) tsStepCl ![(t, u)] ↔ srClSem t u := by
  rw [FOInterpretation.relMap_map]
  match t with
  | Sum.inl (Sum.inl (Sum.inl (σp, k))) =>
      exact (realize_mergeOrdLHom _ _).trans (realize_isClauseF _ _ _ _ _)
  | Sum.inl (Sum.inl (Sum.inr _)) => exact realize_canonF
  | Sum.inl (Sum.inr _) => exact Formula.realize_bot
  | Sum.inr _ => exact Formula.realize_bot

theorem sr_srcCl_iff (t : SRTag B stepS srcS tgtS) (u : Fin (srDim B stepS srcS tgtS) → A) :
    RelMap (M := (srInterp B stepS srcS tgtS).Map A) tsSrcCl ![(t, u)] ↔ srSrcClSem t u := by
  rw [FOInterpretation.relMap_map]
  match t with
  | Sum.inl (Sum.inr (Sum.inl (Sum.inl (σp, k)))) =>
      exact (realize_mergeOrdLHom _ _).trans (realize_isClauseF _ _ _ _ _)
  | Sum.inl (Sum.inr (Sum.inl (Sum.inr _))) => exact realize_canonF
  | Sum.inl (Sum.inl _) => exact Formula.realize_bot
  | Sum.inl (Sum.inr (Sum.inr _)) => exact Formula.realize_bot
  | Sum.inr _ => exact Formula.realize_bot

theorem sr_tgtCl_iff (t : SRTag B stepS srcS tgtS) (u : Fin (srDim B stepS srcS tgtS) → A) :
    RelMap (M := (srInterp B stepS srcS tgtS).Map A) tsTgtCl ![(t, u)] ↔ srTgtClSem t u := by
  rw [FOInterpretation.relMap_map]
  match t with
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl (σp, k)))) =>
      exact (realize_mergeOrdLHom _ _).trans (realize_isClauseF _ _ _ _ _)
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr _))) => exact realize_canonF
  | Sum.inl (Sum.inl _) => exact Formula.realize_bot
  | Sum.inl (Sum.inr (Sum.inl _)) => exact Formula.realize_bot
  | Sum.inr _ => exact Formula.realize_bot

theorem sr_lit_iff (s : Bool) (tc tx : SRTag B stepS srcS tgtS)
    (u x : Fin (srDim B stepS srcS tgtS) → A) :
    RelMap (M := (srInterp B stepS srcS tgtS).Map A) (if s then tsPosIn else tsNegIn)
        ![(tc, u), (tx, x)] ↔ srLitSem s tc tx u x := by
  have hrel : RelMap (M := (srInterp B stepS srcS tgtS).Map A) (if s then tsPosIn else tsNegIn)
        ![(tc, u), (tx, x)] ↔
      (srLitFml B stepS srcS tgtS s tc tx).Realize
        (fun p => ((![((tc, u) : (srInterp B stepS srcS tgtS).Map A), (tx, x)]) p.1).2 p.2) := by
    cases s
    · rw [if_neg (by simp)]
      exact FOInterpretation.relMap_map _ _ tsNegIn _
    · rw [if_pos rfl]
      exact FOInterpretation.relMap_map _ _ tsPosIn _
  rw [hrel]
  match tc with
  | Sum.inl (Sum.inl (Sum.inl (σp, k))) => exact realize_srLitStep s σp k tx _
  | Sum.inl (Sum.inl (Sum.inr _)) => exact realize_srLitStepTop s tx _
  | Sum.inl (Sum.inr (Sum.inl (Sum.inl (σp, k)))) => exact realize_srLitSrc s σp k tx _
  | Sum.inl (Sum.inr (Sum.inl (Sum.inr _))) => exact realize_srLitSrcTop s tx _
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl (σp, k)))) => exact realize_srLitTgt s σp k tx _
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr _))) => exact realize_srLitTgtTop s tx _
  | Sum.inr _ => exact Formula.realize_bot

end Characterizations

/-! ### From clause satisfaction to satisfaction of a kernel

One lemma, instantiated once per clause group: a valuation of the interpreted
instance satisfies every clause of a group exactly when the Tseitin valuation
it induces satisfies every clause of that group's encoding *and* makes the
group's root gate true. The group enters only through the three
characterizations passed as hypotheses. -/

section Semantic

variable {B stepS srcS tgtS} {A : Type} [L.Structure A] [LinearOrder A]

theorem sr_pos_iff (tc tx : SRTag B stepS srcS tgtS)
    (u x : Fin (srDim B stepS srcS tgtS) → A) :
    RelMap (M := (srInterp B stepS srcS tgtS).Map A) tsPosIn ![(tc, u), (tx, x)] ↔
      srLitSem true tc tx u x :=
  sr_lit_iff true tc tx u x

theorem sr_neg_iff (tc tx : SRTag B stepS srcS tgtS)
    (u x : Fin (srDim B stepS srcS tgtS) → A) :
    RelMap (M := (srInterp B stepS srcS tgtS).Map A) tsNegIn ![(tc, u), (tx, x)] ↔
      srLitSem false tc tx u x :=
  sr_lit_iff false tc tx u x

variable {a₀ : A}
  (f : ((L.sum Language.order).sum B.double.lang).Sentence)
  (hctx : maxCtx f ≤ srDim B stepS srcS tgtS)
  (grp : Language.transSys.Relations 1)
  (cl : (Σ m, NodeAt f m) → Fin 3 → SRTag B stepS srcS tgtS)
  (top : SRTag B stepS srcS tgtS)
  (vr : (B.double.ι ⊕ Σ m, NodeAt f m) → SRTag B stepS srcS tgtS)

/-- **Clause satisfaction, group by group**: the clauses of a group hold of a
valuation exactly when the Tseitin clauses of that group's kernel hold of the
induced valuation and the kernel's root gate is true at the padded empty
tuple. -/
theorem clausesHold_group_iff (h₀ : IsBot a₀)
    (hclause : ∀ (t : SRTag B stepS srcS tgtS) (u : Fin (srDim B stepS srcS tgtS) → A),
      RelMap (M := (srInterp B stepS srcS tgtS).Map A) grp ![(t, u)] ↔
        ((∃ σp k, t = cl σp k ∧ IsClauseSem f hctx σp.2 k u) ∨ (t = top ∧ Canon 0 u)))
    (hlitNode : ∀ (s : Bool) (σp : Σ m, NodeAt f m) (k : Fin 3)
        (tx : SRTag B stepS srcS tgtS) (u x : Fin (srDim B stepS srcS tgtS) → A),
      srLitSem s (cl σp k) tx u x ↔ ∃ vt, tx = vr vt ∧ LitSem s f hctx σp.2 k u vt x)
    (hlitTop : ∀ (s : Bool) (tx : SRTag B stepS srcS tgtS)
        (u x : Fin (srDim B stepS srcS tgtS) → A),
      srLitSem s top tx u x ↔
        (s = true ∧ tx = vr (Sum.inr ⟨0, rootAt f⟩) ∧ Canon 0 u ∧ Canon 0 x))
    (ν : (srInterp B stepS srcS tgtS).Map A → Prop) :
    ClausesHold ((srInterp B stepS srcS tgtS).Map A) ν grp ↔
      (SatCond f hctx (fun w u => ν (vr w, u)) ∧
        ν (vr (Sum.inr ⟨0, rootAt f⟩), pad a₀ finZeroElim)) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro m p k u hcl
      obtain ⟨⟨tx, x⟩, hx⟩ :=
        h (cl ⟨m, p⟩ k, u) ((hclause _ u).mpr (Or.inl ⟨⟨m, p⟩, k, rfl, hcl⟩))
      rcases hx with ⟨hpos, hval⟩ | ⟨hneg, hval⟩
      · obtain ⟨vt, rfl, hls⟩ :=
          (hlitNode true ⟨m, p⟩ k tx u x).mp ((sr_pos_iff _ _ u x).mp hpos)
        exact ⟨vt, x, Or.inl ⟨hls, hval⟩⟩
      · obtain ⟨vt, rfl, hls⟩ :=
          (hlitNode false ⟨m, p⟩ k tx u x).mp ((sr_neg_iff _ _ u x).mp hneg)
        exact ⟨vt, x, Or.inr ⟨hls, hval⟩⟩
    · obtain ⟨⟨tx, x⟩, hx⟩ :=
        h (top, pad a₀ finZeroElim) ((hclause _ _).mpr (Or.inr ⟨rfl, canon_pad h₀ 0 _⟩))
      rcases hx with ⟨hpos, hval⟩ | ⟨hneg, hval⟩
      · obtain ⟨-, rfl, -, hcx⟩ := (hlitTop true tx _ x).mp ((sr_pos_iff _ _ _ x).mp hpos)
        have hx0 : x = pad a₀ finZeroElim := by
          rw [← pad_pref_of_canon h₀ (Nat.zero_le _) hcx]
          exact (congrArg (pad a₀) (Subsingleton.elim _ _)).symm
        rw [← hx0]
        exact hval
      · exact absurd ((hlitTop false tx _ x).mp ((sr_neg_iff _ _ _ x).mp hneg)).1 (by simp)
  · rintro ⟨hsat, hroot⟩ ⟨t, u⟩ hc
    rcases (hclause t u).mp hc with ⟨σp, k, rfl, hcl⟩ | ⟨rfl, hu⟩
    · obtain ⟨vt, x, hor⟩ := hsat σp.1 σp.2 k u hcl
      rcases hor with ⟨hls, hval⟩ | ⟨hls, hval⟩
      · exact ⟨(vr vt, x), Or.inl ⟨(sr_pos_iff _ _ u x).mpr
          ((hlitNode true σp k (vr vt) u x).mpr ⟨vt, rfl, hls⟩), hval⟩⟩
      · exact ⟨(vr vt, x), Or.inr ⟨(sr_neg_iff _ _ u x).mpr
          ((hlitNode false σp k (vr vt) u x).mpr ⟨vt, rfl, hls⟩), hval⟩⟩
    · refine ⟨(vr (Sum.inr ⟨0, rootAt f⟩), pad a₀ finZeroElim), Or.inl ⟨?_, hroot⟩⟩
      exact (sr_pos_iff _ _ u _).mpr
        ((hlitTop true _ u _).mpr ⟨rfl, rfl, hu, canon_pad h₀ 0 _⟩)

theorem sr_step_cases (t : SRTag B stepS srcS tgtS) (u : Fin (srDim B stepS srcS tgtS) → A) :
    RelMap (M := (srInterp B stepS srcS tgtS).Map A) tsStepCl ![(t, u)] ↔
      ((∃ σp k, t = tagStepCl σp k
        ∧ IsClauseSem (stepK B stepS) (ctx_step B stepS srcS tgtS) σp.2 k u) ∨
        (t = tagStepTop ∧ Canon 0 u)) := by
  rw [sr_stepCl_iff]
  match t with
  | Sum.inl (Sum.inl (Sum.inl (σp, k))) =>
      simp [srClSem, tagStepCl, tagStepTop]
  | Sum.inl (Sum.inl (Sum.inr _)) =>
      simp [srClSem, tagStepCl, tagStepTop]
  | Sum.inl (Sum.inr _) =>
      simp [srClSem, tagStepCl, tagStepTop]
  | Sum.inr _ =>
      simp [srClSem, tagStepCl, tagStepTop]

theorem sr_step_litNode (s : Bool) (σp : Σ m, NodeAt (stepK B stepS) m) (k : Fin 3)
    (tx : SRTag B stepS srcS tgtS) (u x : Fin (srDim B stepS srcS tgtS) → A) :
    srLitSem s (tagStepCl σp k) tx u x ↔
      ∃ vt, tx = stepVar vt
        ∧ LitSem s (stepK B stepS) (ctx_step B stepS srcS tgtS) σp.2 k u vt x := by
  match tx with
  | Sum.inr (Sum.inl i) =>
      simp [srLitSem, srLitStepSem, stepVar, tagAtom, tagStepGate]
  | Sum.inr (Sum.inr (Sum.inl σq)) =>
      simp [srLitSem, srLitStepSem, stepVar, tagAtom, tagStepGate]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl σq))) =>
      simp [srLitSem, srLitStepSem, stepVar, tagAtom, tagStepGate]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr σq))) =>
      simp [srLitSem, srLitStepSem, stepVar, tagAtom, tagStepGate]
  | Sum.inl _ =>
      simp [srLitSem, srLitStepSem, stepVar, tagAtom, tagStepGate]

theorem sr_step_litTop (s : Bool) (tx : SRTag B stepS srcS tgtS)
    (u x : Fin (srDim B stepS srcS tgtS) → A) :
    srLitSem s tagStepTop tx u x ↔
      (s = true ∧ tx = stepVar (Sum.inr ⟨0, rootAt (stepK B stepS)⟩) ∧ Canon 0 u ∧ Canon 0 x) := by
  match tx with
  | Sum.inr (Sum.inl i) =>
      simp [srLitSem, srLitStepTopSem, stepVar, tagStepGate]
  | Sum.inr (Sum.inr (Sum.inl σq)) =>
      simp [srLitSem, srLitStepTopSem, stepVar, tagStepGate]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl σq))) =>
      simp [srLitSem, srLitStepTopSem, stepVar, tagStepGate]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr σq))) =>
      simp [srLitSem, srLitStepTopSem, stepVar, tagStepGate]
  | Sum.inl _ =>
      simp [srLitSem, srLitStepTopSem, stepVar, tagStepGate]

theorem sr_src_cases (t : SRTag B stepS srcS tgtS) (u : Fin (srDim B stepS srcS tgtS) → A) :
    RelMap (M := (srInterp B stepS srcS tgtS).Map A) tsSrcCl ![(t, u)] ↔
      ((∃ σp k, t = tagSrcCl σp k
        ∧ IsClauseSem (srcK B srcS) (ctx_src B stepS srcS tgtS) σp.2 k u) ∨
        (t = tagSrcTop ∧ Canon 0 u)) := by
  rw [sr_srcCl_iff]
  match t with
  | Sum.inl (Sum.inr (Sum.inl (Sum.inl (σp, k)))) =>
      simp [srSrcClSem, tagSrcCl, tagSrcTop]
  | Sum.inl (Sum.inr (Sum.inl (Sum.inr _))) =>
      simp [srSrcClSem, tagSrcCl, tagSrcTop]
  | Sum.inl (Sum.inl _) =>
      simp [srSrcClSem, tagSrcCl, tagSrcTop]
  | Sum.inl (Sum.inr (Sum.inr _)) =>
      simp [srSrcClSem, tagSrcCl, tagSrcTop]
  | Sum.inr _ =>
      simp [srSrcClSem, tagSrcCl, tagSrcTop]

theorem sr_src_litNode (s : Bool) (σp : Σ m, NodeAt (srcK B srcS) m) (k : Fin 3)
    (tx : SRTag B stepS srcS tgtS) (u x : Fin (srDim B stepS srcS tgtS) → A) :
    srLitSem s (tagSrcCl σp k) tx u x ↔
      ∃ vt, tx = srcVar vt ∧ LitSem s (srcK B srcS) (ctx_src B stepS srcS tgtS) σp.2 k u vt x := by
  match tx with
  | Sum.inr (Sum.inl i) =>
      simp [srLitSem, srLitSrcSem, srcVar, tagAtom, tagSrcGate]
  | Sum.inr (Sum.inr (Sum.inl σq)) =>
      simp [srLitSem, srLitSrcSem, srcVar, tagAtom, tagSrcGate]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl σq))) =>
      simp [srLitSem, srLitSrcSem, srcVar, tagAtom, tagSrcGate]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr σq))) =>
      simp [srLitSem, srLitSrcSem, srcVar, tagAtom, tagSrcGate]
  | Sum.inl _ =>
      simp [srLitSem, srLitSrcSem, srcVar, tagAtom, tagSrcGate]

theorem sr_src_litTop (s : Bool) (tx : SRTag B stepS srcS tgtS)
    (u x : Fin (srDim B stepS srcS tgtS) → A) :
    srLitSem s tagSrcTop tx u x ↔
      (s = true ∧ tx = srcVar (Sum.inr ⟨0, rootAt (srcK B srcS)⟩) ∧ Canon 0 u ∧ Canon 0 x) := by
  match tx with
  | Sum.inr (Sum.inl i) =>
      simp [srLitSem, srLitSrcTopSem, srcVar, tagSrcGate]
  | Sum.inr (Sum.inr (Sum.inl σq)) =>
      simp [srLitSem, srLitSrcTopSem, srcVar, tagSrcGate]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl σq))) =>
      simp [srLitSem, srLitSrcTopSem, srcVar, tagSrcGate]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr σq))) =>
      simp [srLitSem, srLitSrcTopSem, srcVar, tagSrcGate]
  | Sum.inl _ =>
      simp [srLitSem, srLitSrcTopSem, srcVar, tagSrcGate]

theorem sr_tgt_cases (t : SRTag B stepS srcS tgtS) (u : Fin (srDim B stepS srcS tgtS) → A) :
    RelMap (M := (srInterp B stepS srcS tgtS).Map A) tsTgtCl ![(t, u)] ↔
      ((∃ σp k, t = tagTgtCl σp k
        ∧ IsClauseSem (tgtK B tgtS) (ctx_tgt B stepS srcS tgtS) σp.2 k u) ∨
        (t = tagTgtTop ∧ Canon 0 u)) := by
  rw [sr_tgtCl_iff]
  match t with
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl (σp, k)))) =>
      simp [srTgtClSem, tagTgtCl, tagTgtTop]
  | Sum.inl (Sum.inr (Sum.inr (Sum.inr _))) =>
      simp [srTgtClSem, tagTgtCl, tagTgtTop]
  | Sum.inl (Sum.inl _) =>
      simp [srTgtClSem, tagTgtCl, tagTgtTop]
  | Sum.inl (Sum.inr (Sum.inl _)) =>
      simp [srTgtClSem, tagTgtCl, tagTgtTop]
  | Sum.inr _ =>
      simp [srTgtClSem, tagTgtCl, tagTgtTop]

theorem sr_tgt_litNode (s : Bool) (σp : Σ m, NodeAt (tgtK B tgtS) m) (k : Fin 3)
    (tx : SRTag B stepS srcS tgtS) (u x : Fin (srDim B stepS srcS tgtS) → A) :
    srLitSem s (tagTgtCl σp k) tx u x ↔
      ∃ vt, tx = tgtVar vt ∧ LitSem s (tgtK B tgtS) (ctx_tgt B stepS srcS tgtS) σp.2 k u vt x := by
  match tx with
  | Sum.inr (Sum.inl i) =>
      simp [srLitSem, srLitTgtSem, tgtVar, tagAtom, tagTgtGate]
  | Sum.inr (Sum.inr (Sum.inl σq)) =>
      simp [srLitSem, srLitTgtSem, tgtVar, tagAtom, tagTgtGate]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl σq))) =>
      simp [srLitSem, srLitTgtSem, tgtVar, tagAtom, tagTgtGate]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr σq))) =>
      simp [srLitSem, srLitTgtSem, tgtVar, tagAtom, tagTgtGate]
  | Sum.inl _ =>
      simp [srLitSem, srLitTgtSem, tgtVar, tagAtom, tagTgtGate]

theorem sr_tgt_litTop (s : Bool) (tx : SRTag B stepS srcS tgtS)
    (u x : Fin (srDim B stepS srcS tgtS) → A) :
    srLitSem s tagTgtTop tx u x ↔
      (s = true ∧ tx = tgtVar (Sum.inr ⟨0, rootAt (tgtK B tgtS)⟩) ∧ Canon 0 u ∧ Canon 0 x) := by
  match tx with
  | Sum.inr (Sum.inl i) =>
      simp [srLitSem, srLitTgtTopSem, tgtVar, tagTgtGate]
  | Sum.inr (Sum.inr (Sum.inl σq)) =>
      simp [srLitSem, srLitTgtTopSem, tgtVar, tagTgtGate]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl σq))) =>
      simp [srLitSem, srLitTgtTopSem, tgtVar, tagTgtGate]
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr σq))) =>
      simp [srLitSem, srLitTgtTopSem, tgtVar, tagTgtGate]
  | Sum.inl _ =>
      simp [srLitSem, srLitTgtTopSem, tgtVar, tagTgtGate]

end Semantic

/-! ### The two walks correspond

A state of the interpreted transition system is a set of atoms of the first
copy of the doubled block, i.e. an assignment of `B`; a valuation witnessing a
transition or an endpoint condition is the canonical Tseitin valuation of the
corresponding kernel. The two directions use the two translations between
states and assignments, so no round trip is ever needed. -/

section Correspondence

variable {B stepS srcS tgtS} {A : Type} [L.Structure A] [LinearOrder A] {a₀ : A}

/-- The Tseitin valuation of a kernel induced by an assignment of the doubled
block: block atoms take their values, gates their canonical ones. -/
noncomputable def canonTv (μ : B.double.Assignment A)
    (f : ((L.sum Language.order).sum B.double.lang).Sentence)
    (hctx : maxCtx f ≤ srDim B stepS srcS tgtS) :
    (B.double.ι ⊕ Σ m, NodeAt f m) → (Fin (srDim B stepS srcS tgtS) → A) → Prop :=
  fun w u =>
    match w with
    | Sum.inl i => μ i (pref (arity_le_srDim B stepS srcS tgtS i) u)
    | Sum.inr σp => canonVal μ f σp.1 σp.2 (pref ((nodeAt_le_maxCtx f σp.2).trans hctx) u)

theorem padAssign_canonTv (μ : B.double.Assignment A)
    (f : ((L.sum Language.order).sum B.double.lang).Sentence)
    (hctx : maxCtx f ≤ srDim B stepS srcS tgtS) :
    padAssign a₀ (canonTv μ f hctx) = μ := by
  funext i a
  exact congrArg (μ i) (pref_pad a₀ _ a)

theorem padVal_canonTv (μ : B.double.Assignment A)
    (f : ((L.sum Language.order).sum B.double.lang).Sentence)
    (hctx : maxCtx f ≤ srDim B stepS srcS tgtS) :
    padVal a₀ (canonTv μ f hctx) = canonVal μ f := by
  funext m q w
  exact congrArg (canonVal μ f m q) (pref_pad a₀ _ w)

theorem satCond_canonTv (h₀ : IsBot a₀) (μ : B.double.Assignment A)
    (f : ((L.sum Language.order).sum B.double.lang).Sentence)
    (hctx : maxCtx f ≤ srDim B stepS srcS tgtS) :
    SatCond f hctx (canonTv μ f hctx) := by
  refine (satCond_iff_gates h₀ (arity_le_srDim B stepS srcS tgtS) f hctx _).mpr ?_
  rw [padAssign_canonTv, padVal_canonTv]
  exact gates_canonVal μ f

theorem root_canonTv (μ : B.double.Assignment A)
    (f : ((L.sum Language.order).sum B.double.lang).Sentence)
    (hctx : maxCtx f ≤ srDim B stepS srcS tgtS) :
    canonTv μ f hctx (Sum.inr ⟨0, rootAt f⟩) (pad a₀ finZeroElim) ↔
      RealizeWith μ f finZeroElim := by
  have h : (pref ((nodeAt_le_maxCtx f (rootAt f)).trans hctx) (pad a₀ finZeroElim) :
      Fin 0 → A) = finZeroElim := Subsingleton.elim _ _
  change canonVal μ f 0 (rootAt f) _ ↔ _
  rw [h]
  exact canonVal_rootAt μ f finZeroElim

/-- The Tseitin valuation induced by a kernel's satisfaction of its clauses
realizes the kernel. -/
theorem realizeWith_of_satCond (h₀ : IsBot a₀)
    (f : ((L.sum Language.order).sum B.double.lang).Sentence)
    (hctx : maxCtx f ≤ srDim B stepS srcS tgtS)
    (tv : (B.double.ι ⊕ Σ m, NodeAt f m) → (Fin (srDim B stepS srcS tgtS) → A) → Prop)
    (hsat : SatCond f hctx tv) (hroot : tv (Sum.inr ⟨0, rootAt f⟩) (pad a₀ finZeroElim)) :
    RealizeWith (padAssign a₀ tv) f finZeroElim :=
  (gates_realize _ f _
    ((satCond_iff_gates h₀ (arity_le_srDim B stepS srcS tgtS) f hctx tv).mp hsat)
    finZeroElim).mp hroot

/-- Realization of a kernel is realization of the sentence it renames. -/
theorem realizeWith_iff (μ : B.double.Assignment A)
    (f : ((L.sum Language.order).sum B.double.lang).Sentence) :
    RealizeWith μ f finZeroElim ↔ @Sentence.Realize _ A (B.double.structure₁ μ) f :=
  iff_of_eq (congrArg₂
    (fun (v : Empty → A) (xs : Fin 0 → A) =>
      @BoundedFormula.Realize _ A (B.double.structure₁ μ) _ _ f v xs)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _))

/-! #### States -/

/-- The state of the interpreted system carried by an assignment of `B`: the
atoms of the first copy that it satisfies. -/
def srStateOf (ρ : B.Assignment A) : (srInterp B stepS srcS tgtS).Map A → Prop := fun e =>
  match e.1 with
  | Sum.inr (Sum.inl (Sum.inl i)) =>
      ρ i (pref (arity_le_srDim B stepS srcS tgtS (Sum.inl i)) e.2)
  | _ => False

/-- The assignment of `B` read off a state of the interpreted system: its
canonically padded atoms of the first copy. -/
def srAssignOf (a₀ : A) (S : (srInterp B stepS srcS tgtS).Map A → Prop) :
    B.Assignment A :=
  fun i w => S (tagAtom (Sum.inl i), pad a₀ w)

/-- The canonical valuation of the interpreted instance under an assignment of
the doubled block. -/
noncomputable def srCanon (μ : B.double.Assignment A) :
    (srInterp B stepS srcS tgtS).Map A → Prop := fun e =>
  match e.1 with
  | Sum.inr (Sum.inl i) => canonTv μ (stepK B stepS) (ctx_step B stepS srcS tgtS)
      (Sum.inl i) e.2
  | Sum.inr (Sum.inr (Sum.inl σp)) =>
      canonTv μ (stepK B stepS) (ctx_step B stepS srcS tgtS) (Sum.inr σp) e.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl σp))) =>
      canonTv μ (srcK B srcS) (ctx_src B stepS srcS tgtS) (Sum.inr σp) e.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr σp))) =>
      canonTv μ (tgtK B tgtS) (ctx_tgt B stepS srcS tgtS) (Sum.inr σp) e.2
  | Sum.inl _ => False

theorem srCanon_step (μ : B.double.Assignment A) :
    (fun w u => srCanon μ (stepVar w, u)) =
      canonTv μ (stepK B stepS) (ctx_step B stepS srcS tgtS) := by
  funext w u
  match w with
  | Sum.inl i => rfl
  | Sum.inr σp => rfl

theorem srCanon_src (μ : B.double.Assignment A) :
    (fun w u => srCanon μ (srcVar w, u)) =
      canonTv μ (srcK B srcS) (ctx_src B stepS srcS tgtS) := by
  funext w u
  match w with
  | Sum.inl i => rfl
  | Sum.inr σp => rfl

theorem srCanon_tgt (μ : B.double.Assignment A) :
    (fun w u => srCanon μ (tgtVar w, u)) =
      canonTv μ (tgtK B tgtS) (ctx_tgt B stepS srcS tgtS) := by
  funext w u
  match w with
  | Sum.inl i => rfl
  | Sum.inr σp => rfl

/-- The canonical valuation reads the state its assignment's first copy
carries. -/
theorem readsCur_srCanon (μ : B.double.Assignment A) :
    ReadsCur ((srInterp B stepS srcS tgtS).Map A) (srCanon μ)
      (srStateOf (B.fstAssign μ)) := by
  rintro ⟨t, u⟩ ht
  rw [sr_stateVar_iff] at ht
  match t with
  | Sum.inr (Sum.inl (Sum.inl i)) => exact Iff.rfl
  | Sum.inr (Sum.inl (Sum.inr i)) => exact ht.elim
  | Sum.inr (Sum.inr _) => exact ht.elim
  | Sum.inl _ => exact ht.elim

/-- The canonical valuation writes the state its assignment's second copy
carries. -/
theorem writesNext_srCanon (μ : B.double.Assignment A) :
    WritesNext ((srInterp B stepS srcS tgtS).Map A) (srCanon μ)
      (srStateOf (B.sndAssign μ)) := by
  rintro ⟨t, u⟩ ⟨t', u'⟩ ht htt
  rw [sr_stateVar_iff] at ht
  rw [sr_next_iff] at htt
  match t, t' with
  | Sum.inr (Sum.inl (Sum.inl i)), Sum.inr (Sum.inl (Sum.inr i')) =>
      obtain ⟨rfl, rfl⟩ := htt
      exact Iff.rfl
  | Sum.inr (Sum.inl (Sum.inl i)), Sum.inr (Sum.inl (Sum.inl i')) => exact htt.elim
  | Sum.inr (Sum.inl (Sum.inl i)), Sum.inr (Sum.inr _) => exact htt.elim
  | Sum.inr (Sum.inl (Sum.inl i)), Sum.inl _ => exact htt.elim
  | Sum.inr (Sum.inl (Sum.inr i)), _ => exact ht.elim
  | Sum.inr (Sum.inr _), _ => exact ht.elim
  | Sum.inl _, _ => exact ht.elim

end Correspondence

/-! #### From the specification's walk to the interpreted one -/

section Forward

variable {B stepS srcS tgtS} {A : Type} [L.Structure A] [LinearOrder A] {a₀ : A}

/-- Every clause of a group holds of the canonical valuation as soon as the
group's kernel does. -/
private theorem clausesHold_canon_step (h₀ : IsBot a₀) (μ : B.double.Assignment A)
    (h : RealizeWith μ (stepK B stepS) finZeroElim) :
    ClausesHold ((srInterp B stepS srcS tgtS).Map A) (srCanon μ) tsStepCl := by
  refine (clausesHold_group_iff (stepK B stepS) (ctx_step B stepS srcS tgtS) tsStepCl
    tagStepCl tagStepTop stepVar h₀ sr_step_cases sr_step_litNode sr_step_litTop _).mpr ?_
  rw [srCanon_step]
  exact ⟨satCond_canonTv h₀ μ (stepK B stepS) (ctx_step B stepS srcS tgtS),
    (root_canonTv μ (stepK B stepS) (ctx_step B stepS srcS tgtS)).mpr h⟩

private theorem clausesHold_canon_src (h₀ : IsBot a₀) (μ : B.double.Assignment A)
    (h : RealizeWith μ (srcK B srcS) finZeroElim) :
    ClausesHold ((srInterp B stepS srcS tgtS).Map A) (srCanon μ) tsSrcCl := by
  refine (clausesHold_group_iff (srcK B srcS) (ctx_src B stepS srcS tgtS) tsSrcCl
    tagSrcCl tagSrcTop srcVar h₀ sr_src_cases sr_src_litNode sr_src_litTop _).mpr ?_
  rw [srCanon_src]
  exact ⟨satCond_canonTv h₀ μ (srcK B srcS) (ctx_src B stepS srcS tgtS),
    (root_canonTv μ (srcK B srcS) (ctx_src B stepS srcS tgtS)).mpr h⟩

private theorem clausesHold_canon_tgt (h₀ : IsBot a₀) (μ : B.double.Assignment A)
    (h : RealizeWith μ (tgtK B tgtS) finZeroElim) :
    ClausesHold ((srInterp B stepS srcS tgtS).Map A) (srCanon μ) tsTgtCl := by
  refine (clausesHold_group_iff (tgtK B tgtS) (ctx_tgt B stepS srcS tgtS) tsTgtCl
    tagTgtCl tagTgtTop tgtVar h₀ sr_tgt_cases sr_tgt_litNode sr_tgt_litTop _).mpr ?_
  rw [srCanon_tgt]
  exact ⟨satCond_canonTv h₀ μ (tgtK B tgtS) (ctx_tgt B stepS srcS tgtS),
    (root_canonTv μ (tgtK B tgtS) (ctx_tgt B stepS srcS tgtS)).mpr h⟩

/-- A transition of the specification is a transition of the interpreted
system. -/
theorem stepRel_srStateOf (h₀ : IsBot a₀) (ρ σ : B.Assignment A)
    (h : @Sentence.Realize _ A (B.structure₂ ρ σ) stepS) :
    StepRel ((srInterp B stepS srcS tgtS).Map A) (srStateOf ρ) (srStateOf σ) := by
  refine ⟨srCanon (B.joinAssign ρ σ), clausesHold_canon_step h₀ _ ?_,
    readsCur_srCanon _, writesNext_srCanon _⟩
  exact (realizeWith_iff _ _).mpr ((realize_blockPairLHom B ρ σ stepS).mpr h)

/-- A source state of the specification is a source state of the interpreted
system. -/
theorem isStart_srStateOf (h₀ : IsBot a₀) (ρ : B.Assignment A)
    (h : @Sentence.Realize _ A (B.structure₁ ρ) srcS) :
    IsStart ((srInterp B stepS srcS tgtS).Map A) (srStateOf ρ) := by
  refine ⟨srCanon (B.joinAssign ρ ρ), clausesHold_canon_src h₀ _ ?_, readsCur_srCanon _⟩
  exact (realizeWith_iff _ _).mpr ((realize_blockFstLHom B (B.joinAssign ρ ρ) srcS).mpr h)

/-- A target state of the specification is a target state of the interpreted
system. -/
theorem isGoal_srStateOf (h₀ : IsBot a₀) (ρ : B.Assignment A)
    (h : @Sentence.Realize _ A (B.structure₁ ρ) tgtS) :
    IsGoal ((srInterp B stepS srcS tgtS).Map A) (srStateOf ρ) := by
  refine ⟨srCanon (B.joinAssign ρ ρ), clausesHold_canon_tgt h₀ _ ?_, readsCur_srCanon _⟩
  exact (realizeWith_iff _ _).mpr ((realize_blockFstLHom B (B.joinAssign ρ ρ) tgtS).mpr h)

end Forward

/-! #### From the interpreted walk back to the specification's -/

section Backward

variable {B stepS srcS tgtS} {A : Type} [L.Structure A] [LinearOrder A] {a₀ : A}

/-- A transition of the interpreted system is a transition of the
specification, between the assignments its two states carry. -/
theorem realize_step_of_stepRel (h₀ : IsBot a₀)
    (S S' : (srInterp B stepS srcS tgtS).Map A → Prop)
    (h : StepRel ((srInterp B stepS srcS tgtS).Map A) S S') :
    @Sentence.Realize _ A
      (B.structure₂ (srAssignOf a₀ S) (srAssignOf a₀ S')) stepS := by
  obtain ⟨ν, hcl, hr, hw⟩ := h
  obtain ⟨hsat, hroot⟩ := (clausesHold_group_iff (stepK B stepS)
    (ctx_step B stepS srcS tgtS) tsStepCl tagStepCl tagStepTop stepVar h₀
    sr_step_cases sr_step_litNode sr_step_litTop ν).mp hcl
  have hreal := realizeWith_of_satCond h₀ (stepK B stepS) (ctx_step B stepS srcS tgtS)
    _ hsat hroot
  have hpa : padAssign a₀ (fun w u => ν (stepVar w, u)) =
      B.joinAssign (srAssignOf a₀ S) (srAssignOf a₀ S') := by
    funext i a
    match i with
    | Sum.inl j =>
        exact propext (hr (tagAtom (Sum.inl j), pad a₀ a)
          ((sr_stateVar_iff _ _).mpr trivial))
    | Sum.inr j =>
        exact propext (hw (tagAtom (Sum.inl j), pad a₀ a) (tagAtom (Sum.inr j), pad a₀ a)
          ((sr_stateVar_iff _ _).mpr trivial) ((sr_next_iff _ _ _ _).mpr ⟨rfl, rfl⟩))
  rw [hpa] at hreal
  exact (realize_blockPairLHom B _ _ stepS).mp ((realizeWith_iff _ _).mp hreal)

/-- A source state of the interpreted system carries an assignment satisfying
the source sentence. -/
theorem realize_src_of_isStart (h₀ : IsBot a₀)
    (S : (srInterp B stepS srcS tgtS).Map A → Prop)
    (h : IsStart ((srInterp B stepS srcS tgtS).Map A) S) :
    @Sentence.Realize _ A (B.structure₁ (srAssignOf a₀ S)) srcS := by
  obtain ⟨ν, hcl, hr⟩ := h
  obtain ⟨hsat, hroot⟩ := (clausesHold_group_iff (srcK B srcS)
    (ctx_src B stepS srcS tgtS) tsSrcCl tagSrcCl tagSrcTop srcVar h₀
    sr_src_cases sr_src_litNode sr_src_litTop ν).mp hcl
  have hreal := realizeWith_of_satCond h₀ (srcK B srcS) (ctx_src B stepS srcS tgtS)
    _ hsat hroot
  have hfst : B.fstAssign (padAssign a₀ (fun w u => ν (srcVar w, u))) =
      srAssignOf a₀ S := by
    funext j a
    exact propext (hr (tagAtom (Sum.inl j), pad a₀ a)
      ((sr_stateVar_iff _ _).mpr trivial))
  have hres := (realize_blockFstLHom B _ srcS).mp ((realizeWith_iff _ _).mp hreal)
  rwa [hfst] at hres

/-- A target state of the interpreted system carries an assignment satisfying
the target sentence. -/
theorem realize_tgt_of_isGoal (h₀ : IsBot a₀)
    (S : (srInterp B stepS srcS tgtS).Map A → Prop)
    (h : IsGoal ((srInterp B stepS srcS tgtS).Map A) S) :
    @Sentence.Realize _ A (B.structure₁ (srAssignOf a₀ S)) tgtS := by
  obtain ⟨ν, hcl, hr⟩ := h
  obtain ⟨hsat, hroot⟩ := (clausesHold_group_iff (tgtK B tgtS)
    (ctx_tgt B stepS srcS tgtS) tsTgtCl tagTgtCl tagTgtTop tgtVar h₀
    sr_tgt_cases sr_tgt_litNode sr_tgt_litTop ν).mp hcl
  have hreal := realizeWith_of_satCond h₀ (tgtK B tgtS) (ctx_tgt B stepS srcS tgtS)
    _ hsat hroot
  have hfst : B.fstAssign (padAssign a₀ (fun w u => ν (tgtVar w, u))) =
      srAssignOf a₀ S := by
    funext j a
    exact propext (hr (tagAtom (Sum.inl j), pad a₀ a)
      ((sr_stateVar_iff _ _).mpr trivial))
  have hres := (realize_blockFstLHom B _ tgtS).mp ((realizeWith_iff _ _).mp hreal)
  rwa [hfst] at hres

end Backward

/-! ### Correctness of the interpretation -/

section Correct

variable {B stepS srcS tgtS} {A : Type} [L.Structure A] [LinearOrder A] {a₀ : A}

/-- The transition relation of the specification, spelled out. -/
private def specStep (ρ σ : B.Assignment A) : Prop :=
  @Sentence.Realize _ A (B.structure₂ ρ σ) stepS

private theorem reach_srStateOf (h₀ : IsBot a₀) {ρ σ : B.Assignment A}
    (h : Relation.ReflTransGen (specStep (stepS := stepS)) ρ σ) :
    Relation.ReflTransGen (StepRel ((srInterp B stepS srcS tgtS).Map A))
      (srStateOf ρ) (srStateOf σ) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih => exact ih.tail (stepRel_srStateOf h₀ c d hcd)

private theorem reach_srAssignOf (h₀ : IsBot a₀)
    {S S' : (srInterp B stepS srcS tgtS).Map A → Prop}
    (h : Relation.ReflTransGen (StepRel ((srInterp B stepS srcS tgtS).Map A)) S S') :
    Relation.ReflTransGen (specStep (stepS := stepS))
      (srAssignOf a₀ S) (srAssignOf a₀ S') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih => exact ih.tail (realize_step_of_stepRel h₀ c d hcd)

/-- **Correctness of the interpretation**: the interpreted transition system
reaches a target state from a source state exactly when the specification
accepts the input structure. -/
theorem srInterp_correct (h₀ : IsBot a₀) :
    SuccinctReachable ((srInterp B stepS srcS tgtS).Map A) ↔
      ∃ ρ σ : B.Assignment A,
        (@Sentence.Realize _ A (B.structure₁ ρ) srcS) ∧
          (@Sentence.Realize _ A (B.structure₁ σ) tgtS) ∧
            Relation.ReflTransGen (specStep (stepS := stepS)) ρ σ := by
  constructor
  · rintro ⟨S, S', hst, hgo, hreach⟩
    exact ⟨srAssignOf a₀ S, srAssignOf a₀ S', realize_src_of_isStart h₀ S hst,
      realize_tgt_of_isGoal h₀ S' hgo, reach_srAssignOf h₀ hreach⟩
  · rintro ⟨ρ, σ, hsrc, htgt, hreach⟩
    exact ⟨srStateOf ρ, srStateOf σ, isStart_srStateOf h₀ ρ hsrc,
      isGoal_srStateOf h₀ σ htgt, reach_srStateOf h₀ hreach⟩

end Correct

end SuccinctReachHard

/-! ### The discharge -/

open SuccinctReachHard in
/-- **The generic reduction to SUCCINCT-REACH**: an ordered first-order
reduction from any problem defined, on nonempty finite ordered structures, by
an SO(TC) specification. -/
noncomputable def sotcReduction {L : Language.{0, 0}} [L.IsRelational] (Q : DecisionProblem L)
    (spec : SOTCSpec L)
    (hspec : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      Q A ↔ spec.Accepts A) : Q ≤ᶠᵒ[≤] SUCCINCTREACH where
  Tag := SRTag spec.B spec.step spec.src spec.tgt
  dim := srDim spec.B spec.step spec.src spec.tgt
  toInterpretation := srInterp spec.B spec.step spec.src spec.tgt
  correct A _ _ _ _ := by
    obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
    haveI := (srInterp spec.B spec.step spec.src spec.tgt).map_finite A
    haveI := (srInterp spec.B spec.step spec.src spec.tgt).map_nonempty A
    exact (hspec A).trans (srInterp_correct ha₀).symm

/-- **Hardness**: every SO(TC) definable problem admits an ordered first-order
reduction to SUCCINCT-REACH. -/
theorem succinctReach_hard_of_sotcDefinable :
    ∀ {L : Language.{0, 0}} [L.IsRelational] (Q : DecisionProblem L),
      SOTCDefinable Q → Nonempty (Q ≤ᶠᵒ[≤] SUCCINCTREACH) := by
  rintro L _ Q ⟨spec, hspec⟩
  exact ⟨sotcReduction Q spec hspec⟩

/-- **SUCCINCT-REACH is PSPACE-complete.** Membership is
`DescriptiveComplexity.succinctReach_mem_PSPACE`, the SO(TC) specification whose
states are the states of the transition system; hardness is
`DescriptiveComplexity.succinctReach_hard_of_sotcDefinable`, the three-group Tseitin
discharge. -/
theorem SUCCINCTREACH_PSPACE_complete : PSPACE.Complete SUCCINCTREACH :=
  ⟨succinctReach_mem_PSPACE,
    PSPACE_hard_of_sotcDefinable SUCCINCTREACH fun Q hQ =>
      (succinctReach_hard_of_sotcDefinable Q hQ).map OrderedFOReduction.toRel⟩


end DescriptiveComplexity
