/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CliqueFamily.CountingAll
import DescriptiveComplexity.Problems.CliqueFamily.Stretch

/-!
# #BIS and #PP2DNF: counting the independent sets of a bipartite graph

A *bipartite graph* is given with its bipartition
(`FirstOrder.Language.bipGraph`): a unary relation marks the left side, the
right side is the rest, and only the edges from a left vertex to a right vertex
are read. `DescriptiveComplexity.SharpBIS` is the number of its independent
sets, the sets with no edge from a left member to a right member.

Like the count of all the independent sets of a graph, it is one-call
`#P`-complete and not parsimoniously
(`DescriptiveComplexity.sharpBIS_sharpP_oneCallComplete`). Hardness is from that
problem, by stretching (`DescriptiveComplexity.stretchInterp`): every edge is
replaced by `2n` paths of length two through new middle vertices, which form
the left side. An independent set of the result is any set `S` of vertices and
any set of middles of the edges with no endpoint in `S`, so the oracle answers
`∑ S, (2 ^ (2n)) ^ e(S)`, and the remainder modulo `2 ^ (2n)` counts the sets
with `e(S) = 0`, the complements of the independent sets
(`DescriptiveComplexity.card_stretchIndep_mod`).

`DescriptiveComplexity.SharpPP2DNF` is the same data read as a formula: one
variable per vertex and one term `x ∧ y` per edge, a *partitioned positive
2-DNF*. Its models are the sets of vertices that are not independent, so
`#BIS + #PP2DNF = 2 ^ n` (`DescriptiveComplexity.sharpBIS_add_sharpPP2DNF`) and
it is one-call `#P`-complete as well
(`DescriptiveComplexity.sharpPP2DNF_sharpP_oneCallComplete`).

In the literature these are the two *partitioned positive* problems. The
independent sets of a bipartite graph are the complements of its vertex
covers, i.e., of the models of `⋀ (x ∨ y)` over its edges, so #BIS is
#PP2CNF, whose `#P`-hardness is due to
[Provan and Ball 1983][provan1983complexity]; #PP2DNF is its dual. This is
the form in which [Dalvi and Suciu 2012][dalvi2012dichotomy] (Theorem 5.1
there, and Proposition 5.2 for the query `R(x), S(x, y), T(y)`) use it. The
hardness proved here is by a different route, with one oracle call, and is
not taken from those papers.

The interpretation is three-dimensional and relativized: the vertices are the
diagonal triples of one tag, and each of two other tags carries the triples
`(u, v, i)` with `u – v` an edge.
-/

namespace FirstOrder

namespace Language

/-- The relational language of bipartite graphs given with their bipartition. -/
fo_language bipGraph with bg where
  /-- `left a`: the vertex `a` is on the left side. -/
  left : 1
  /-- `edge a b`: there is an edge between `a` and `b`; read for `a` on the
  left and `b` on the right. -/
  edge : 2

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Shorthands

variable {A : Type} [Language.bipGraph.Structure A]

fo_predicates Language.bipGraph bg

end Shorthands

/-! ### The problem -/

/-- The set `S` is independent in a bipartite graph: no edge goes from a left
member of `S` to a right member of `S`. -/
def BipIndep (A : Type) [Language.bipGraph.Structure A] (S : A → Prop) : Prop :=
  ∀ x y : A, S x → S y → BGLeft x → ¬BGLeft y → ¬BGEdge x y

section Kernel

open SOBlock

/-- The vocabulary of the kernel: bipartite graphs with one unary relation
variable. -/
abbrev bisSOLang : Language := Language.bipGraph.sum satAssignBlock.lang

/-- The left-side symbol, in the kernel vocabulary. -/
abbrev kbLeftSym : bisSOLang.Relations 1 := Sum.inl bgLeft

/-- The edge symbol, in the kernel vocabulary. -/
abbrev kbEdgeSym : bisSOLang.Relations 2 := Sum.inl bgEdge

/-- The guessed set, in the kernel vocabulary. -/
abbrev kbSetSym : bisSOLang.Relations 1 := Sum.inr satNuSym

/-- The first-order kernel: no edge from a left member to a right member. -/
noncomputable def bisKernel : bisSOLang.Sentence :=
  fo% ∀ x y, kbSetSym(x) → kbSetSym(y) → kbLeftSym(x) → ¬ kbLeftSym(y) → ¬ kbEdgeSym(x, y)

theorem realize_bisKernel {A : Type} [Language.bipGraph.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize bisSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) bisKernel) ↔
      BipIndep A ((satAssignEquiv A).symm ρ) := by
  let := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := bisSOLang) (M := A) kbSetSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [bisKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_not, Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var,
    Sum.elim_inr, Language.relMap_sumInl, hsub]
  constructor
  · intro h x y hx hy hl hr
    exact h ![x, y] hx hy hl hr
  · intro h w hx hy hl hr
    exact h (w 0) (w 1) hx hy hl hr

end Kernel

/-- The number of independent sets of a bipartite graph is the number of
witnesses of the kernel. -/
theorem card_bipIndep_eq_witnessCount (A : Type) [Language.bipGraph.Structure A] :
    Nat.card {S : A → Prop // BipIndep A S} = witnessCount satAssignBlock bisKernel A :=
  Nat.card_congr (Equiv.subtypeEquiv (satAssignEquiv A) fun S => by
    rw [realize_bisKernel, Equiv.symm_apply_apply])

/-- **#BIS**: the number of independent sets of a bipartite graph. -/
noncomputable def SharpBIS : CountingProblem Language.bipGraph where
  Count := fun A inst => Nat.card {S : A → Prop // @BipIndep A inst S}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_bipIndep_eq_witnessCount A, card_bipIndep_eq_witnessCount B]
    exact witnessCount_iso satAssignBlock bisKernel e

theorem sharpBIS_apply (A : Type) [Language.bipGraph.Structure A] :
    SharpBIS A = Nat.card {S : A → Prop // BipIndep A S} :=
  rfl

/-- **#BIS is in `#P`.** -/
theorem sharpBIS_mem_sharpP : SharpBIS ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => (card_bipIndep_eq_witnessCount A).symm)
    (sharpPDefinable_ofKernel satAssignBlock bisKernel)

/-! ### The stretched graph -/

/-- Domain of the middle vertices: the triples whose first two coordinates are
the ends of an edge. -/
noncomputable def stretchMidDom : (Language.graph.sum Language.order).Formula (Fin 3) :=
  (∼((Term.var 0).equal (Term.var 1))) ⊓
    LHom.sumInl.onFormula (Language.adj.formula₂ (Term.var 0) (Term.var 1))

/-- The stretched graph, drawn in triples: the tag `none` carries the vertices,
on the diagonal, and each tag `some b` the middle vertices `(u, v, i)` of the
edge `u – v`, adjacent to `u` and to `v`. The middle vertices are the left
side. -/
noncomputable def stretchInterp :
    RelFOInterpretation (Language.graph.sum Language.order) Language.bipGraph (Option Bool) 3 where
  relFormula {n} R :=
    match n, R with
    | _, .left => fun t =>
      match t 0 with
      | none => ⊥
      | some _ => ⊤
    | _, .edge => fun t =>
      match t 0, t 1 with
      | some _, none => fo%⟨u, v⟩ (v ≐ u) ∨ (v ≐ u[1])
      | _, _ => ⊥
  domFormula := fun t =>
    match t with
    | none => (Term.var 0).equal (Term.var 1) ⊓ (Term.var 1).equal (Term.var 2)
    | some _ => stretchMidDom

section Stretch

variable {A : Type} [Language.graph.Structure A] [LinearOrder A]

theorem realize_stretchMidDom (w : Fin 3 → A) :
    stretchMidDom.Realize w ↔ w 0 ≠ w 1 ∧ RelMap Language.adj ![w 0, w 1] := by
  simp [stretchMidDom, LHom.realize_onFormula, Formula.realize_rel₂]

/-- The points of the stretched graph: a vertex, or a middle vertex of an
edge. -/
noncomputable def stretchEquiv : stretchInterp.MapRel A ≃
    A ⊕ EdgePair (fun a b : A => RelMap Language.adj ![a, b]) × (Bool × A) where
  toFun x :=
    match x with
    | ⟨(none, w), _⟩ => .inl (w 0)
    | ⟨(some b, w), hw⟩ => .inr (⟨(w 0, w 1), (realize_stretchMidDom w).mp hw⟩, (b, w 2))
  invFun y :=
    match y with
    | .inl a => ⟨(none, ![a, a, a]), by simp [stretchInterp]⟩
    | .inr q => ⟨(some q.2.1, ![q.1.1.1, q.1.1.2, q.2.2]),
        (realize_stretchMidDom _).mpr q.1.2⟩
  left_inv := by
    rintro ⟨⟨t, w⟩, hw⟩
    cases t with
    | none =>
      have h : w 0 = w 1 ∧ w 1 = w 2 := by simpa [stretchInterp] using hw
      refine Subtype.ext (Prod.ext rfl (funext fun j => ?_))
      fin_cases j
      · rfl
      · exact h.1
      · exact h.1.trans h.2
    | some b =>
      refine Subtype.ext (Prod.ext rfl (funext fun j => ?_))
      fin_cases j <;> rfl
  right_inv := by
    rintro (a | q) <;> rfl

theorem stretch_left (x : stretchInterp.MapRel A) :
    BGLeft x ↔ (stretchEquiv x).isRight = true := by
  rw [BGLeft, RelFOInterpretation.relMap_mapRel]
  obtain ⟨⟨t, w⟩, hw⟩ := x
  cases t with
  | none =>
    change _ ↔ false = true
    simp [stretchInterp]
  | some b =>
    change _ ↔ true = true
    simp [stretchInterp]

theorem stretch_edge (x y : stretchInterp.MapRel A) :
    BGEdge x y ↔ stretchEdge (fun a b : A => RelMap Language.adj ![a, b])
      (stretchEquiv x) (stretchEquiv y) := by
  rw [BGEdge, RelFOInterpretation.relMap_mapRel]
  obtain ⟨⟨t, w⟩, hw⟩ := x
  obtain ⟨⟨t', w'⟩, hw'⟩ := y
  cases t with
  | none =>
    change _ ↔ False
    cases t' <;> simp [stretchInterp]
  | some b =>
    cases t' with
    | none =>
      change _ ↔ (w' 0 = w 0 ∨ w' 0 = w 1)
      simp [stretchInterp]
    | some b' =>
      change _ ↔ False
      simp [stretchInterp]

/-- The independent sets of the interpreted bipartite graph are those of the
stretched graph. -/
theorem sharpBIS_stretch :
    SharpBIS (stretchInterp.MapRel A) =
      Nat.card {T : A ⊕ EdgePair (fun a b : A => RelMap Language.adj ![a, b]) × (Bool × A) →
        Prop // StretchIndep (fun a b : A => RelMap Language.adj ![a, b]) T} :=
  Nat.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr stretchEquiv (Equiv.refl Prop))
    fun S => stretchIndep_equiv_iff stretchEquiv stretch_left stretch_edge S)

end Stretch

/-! ### The reduction -/

/-- **Counting the independent sets of a graph reduces to #BIS with one
call**: the number of independent sets of the stretched graph, modulo
`2 ^ (2n)`, is the number of independent sets of the graph. -/
noncomputable def sharpAllIndependentSets_oneCall_sharpBIS :
    SharpAllIndependentSets ≤ᶜ[≤] SharpBIS where
  Tag := Option Bool
  dim := 3
  toRelInterpretation := stretchInterp
  dom_nonempty := fun A _ _ _ _ =>
    ⟨none, fun _ => Classical.arbitrary A, by simp [stretchInterp]⟩
  post := .mod .oracle (.pow2 (.mul (.num 2) .univ))
  correct := fun A _ _ _ _ => by
    change SharpAllIndependentSets A =
      SharpBIS (stretchInterp.MapRel A) %
        2 ^ (2 * (PolyTerm.univ : PolyTerm Language.graph).eval A)
    have hpos : 0 < Nat.card A := Nat.card_pos
    have hW : Nat.card (Bool × A) = 2 * Nat.card A := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_bool]
    rw [PolyTerm.eval_univ, sharpBIS_stretch, ← hW,
      card_stretchIndep_mod _ (by rw [hW]; omega), sharpAllIndependentSets_apply]

/-- **#BIS is one-call `#P`-hard.** -/
theorem sharpBIS_sharpP_oneCallHard : SharpP.OneCallHard SharpBIS :=
  CountingClass.OneCallHard.of_oneCall sharpAllIndependentSets_oneCall_sharpBIS
    sharpAllIndependentSets_sharpP_oneCallHard

/-- **#BIS is one-call `#P`-complete**: counting the independent sets of a
bipartite graph is in `#P`, and every problem of `#P` reduces to it with one
call. -/
theorem sharpBIS_sharpP_oneCallComplete : SharpP.OneCallComplete SharpBIS :=
  .of_mem sharpBIS_mem_sharpP sharpBIS_sharpP_oneCallHard

/-! ### #PP2DNF -/

/-- The set `S` of true variables satisfies the partitioned positive 2-DNF
formula of a bipartite graph – one variable per vertex, one term `x ∧ y` per
edge from a left vertex `x` to a right vertex `y`: some term has both its
variables true. -/
def Pp2dnfModel (A : Type) [Language.bipGraph.Structure A] (S : A → Prop) : Prop :=
  ∃ x y : A, S x ∧ S y ∧ BGLeft x ∧ ¬BGLeft y ∧ BGEdge x y

/-- The models of the formula are the sets of vertices that are not
independent. -/
theorem pp2dnfModel_iff_not_bipIndep (A : Type) [Language.bipGraph.Structure A]
    (S : A → Prop) : Pp2dnfModel A S ↔ ¬BipIndep A S := by
  constructor
  · rintro ⟨x, y, hx, hy, hl, hr, he⟩ h
    exact h x y hx hy hl hr he
  · intro h
    by_contra hno
    exact h fun x y hx hy hl hr he => hno ⟨x, y, hx, hy, hl, hr, he⟩

/-- The number of models of the formula is the number of witnesses of the
negated kernel of #BIS. -/
theorem card_pp2dnfModel_eq_witnessCount (A : Type) [Language.bipGraph.Structure A] :
    Nat.card {S : A → Prop // Pp2dnfModel A S} = witnessCount satAssignBlock (∼bisKernel) A :=
  Nat.card_congr (Equiv.subtypeEquiv (satAssignEquiv A) fun S => by
    let := satAssignBlock.structure (satAssignEquiv A S)
    rw [Sentence.Realize, Formula.realize_not, ← Sentence.Realize, realize_bisKernel,
      Equiv.symm_apply_apply]
    exact pp2dnfModel_iff_not_bipIndep A S)

/-- **#PP2DNF**: the number of satisfying assignments of a partitioned
positive 2-DNF formula, presented as its bipartite graph. -/
noncomputable def SharpPP2DNF : CountingProblem Language.bipGraph where
  Count := fun A inst => Nat.card {S : A → Prop // @Pp2dnfModel A inst S}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_pp2dnfModel_eq_witnessCount A, card_pp2dnfModel_eq_witnessCount B]
    exact witnessCount_iso satAssignBlock (∼bisKernel) e

theorem sharpPP2DNF_apply (A : Type) [Language.bipGraph.Structure A] :
    SharpPP2DNF A = Nat.card {S : A → Prop // Pp2dnfModel A S} :=
  rfl

/-- **#PP2DNF is in `#P`.** -/
theorem sharpPP2DNF_mem_sharpP : SharpPP2DNF ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => (card_pp2dnfModel_eq_witnessCount A).symm)
    (sharpPDefinable_ofKernel satAssignBlock (∼bisKernel))

/-- **Independent sets and models share out the sets of vertices**:
`#BIS + #PP2DNF = 2 ^ n`. -/
theorem sharpBIS_add_sharpPP2DNF (A : Type) [Language.bipGraph.Structure A] [Finite A] :
    SharpBIS A + SharpPP2DNF A = 2 ^ Nat.card A := by
  have h1 : SharpPP2DNF A = Nat.card {S : A → Prop // ¬BipIndep A S} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun S => pp2dnfModel_iff_not_bipIndep A S)
  have h2 := card_not_add_card (V := A → Prop) (BipIndep A)
  have h3 : Nat.card (A → Prop) = 2 ^ Nat.card A := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_prop]
  rw [h1, sharpBIS_apply, ← h3, ← h2]
  exact Nat.add_comm _ _

/-- **#BIS reduces to #PP2DNF with one call**, on the same instance:
`#BIS = 2 ^ n - #PP2DNF`. -/
noncomputable def sharpBIS_oneCall_sharpPP2DNF : SharpBIS ≤ᶜ[≤] SharpPP2DNF :=
  (ParsimoniousReduction.refl SharpPP2DNF).toOneCall.ofPost (.sub (.pow2 .univ) .oracle)
    fun A _ _ _ _ => by
      change SharpBIS A =
        2 ^ (PolyTerm.univ : PolyTerm Language.bipGraph).eval A - SharpPP2DNF A
      rw [PolyTerm.eval_univ, ← sharpBIS_add_sharpPP2DNF A]
      exact (Nat.add_sub_cancel_right ..).symm

/-- **#PP2DNF is one-call `#P`-hard.** -/
theorem sharpPP2DNF_sharpP_oneCallHard : SharpP.OneCallHard SharpPP2DNF :=
  CountingClass.OneCallHard.of_oneCall sharpBIS_oneCall_sharpPP2DNF sharpBIS_sharpP_oneCallHard

/-- **#PP2DNF is one-call `#P`-complete.** -/
theorem sharpPP2DNF_sharpP_oneCallComplete : SharpP.OneCallComplete SharpPP2DNF :=
  .of_mem sharpPP2DNF_mem_sharpP sharpPP2DNF_sharpP_oneCallHard

end DescriptiveComplexity
