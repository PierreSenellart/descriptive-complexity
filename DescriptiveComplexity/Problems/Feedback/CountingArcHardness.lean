/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Feedback.SplitBundle
import DescriptiveComplexity.Problems.CliqueFamily.CountingHardness
import DescriptiveComplexity.Counting.Subtractive

/-!
# #Feedback Arc Set is parsimoniously `#P`-complete

`DescriptiveComplexity.sharpFeedbackArcSet_sharpP_parsimoniousComplete`, by a reduction
from #1-in-SAT (`DescriptiveComplexity.sharpOneInSat_ordered_parsimonious_sharpFeedbackArcSet`).

The reduction is the composite of two interpretations, and the second is
correct only on the outputs of the first:

* `DescriptiveComplexity.OneInToClique.oneInToClique` sends a CNF formula to a marked
  graph whose cliques of the threshold size are its exactly-one models – and
  which has **no larger clique**
  (`DescriptiveComplexity.OneInToClique.ncard_clique_le`);
* `DescriptiveComplexity.CliqueFas.cliqueFasInterp` sends a marked graph to its conflict
  split graph (`DescriptiveComplexity.Problems.Feedback.SplitBundle`), whose feedback
  arc sets of the threshold size are the cliques of the threshold size of the
  graph *provided it has no larger clique*
  (`DescriptiveComplexity.CliqueFas.sharpFeedbackArcSet_cliqueFas`).

So this is not a reduction from #Clique: on a graph with a clique above the
threshold the second interpretation counts too much, a feedback arc set being
free to waste arcs. A composition under a promise is what
`DescriptiveComplexity.OrderedParsimoniousReduction.transPromise` provides.

The tagged pairs that are no vertex of the split graph are isolated, and an
isolated vertex changes nothing to a set of arcs
(`DescriptiveComplexity.fasOfSizeOnEmbEquiv`): no domain formula is needed.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Feedback arc sets ignore isolated vertices -/

section Embedding

variable {W M : Type}

/-- **Feedback arc sets through an embedding**: if the arcs and the marked
pairs of a graph all lie in the image of an injection, its feedback arc sets
of the threshold size are those of the graph it is the image of. -/
def fasOfSizeOnEmbEquiv (emb : W → M) (hinj : Function.Injective emb)
    {AdjW KW : W → W → Prop} {AdjM KM : M → M → Prop}
    (hadj : ∀ p q, AdjM p q ↔ ∃ u v, p = emb u ∧ q = emb v ∧ AdjW u v)
    (hK : ∀ p q, KM p q ↔ ∃ u v, p = emb u ∧ q = emb v ∧ KW u v) :
    {F : M → M → Prop // FasOfSizeOn AdjM KM F} ≃
      {F : W → W → Prop // FasOfSizeOn AdjW KW F} where
  toFun F := ⟨fun u v => F.1 (emb u) (emb v), fun u v h => by
      obtain ⟨u', v', hu, hv, h'⟩ := (hadj _ _).mp (F.2.1 _ _ h)
      rw [hinj hu, hinj hv]
      exact h', fun u hu => by
      have hlift : ∀ a b, Relation.TransGen (UncutArc AdjW fun u v => F.1 (emb u) (emb v)) a b →
          Relation.TransGen (UncutArc AdjM F.1) (emb a) (emb b) := by
        intro a b hab
        induction hab with
        | single h => exact .single ⟨(hadj _ _).mpr ⟨_, _, rfl, rfl, h.1⟩, h.2⟩
        | tail _ h ih => exact ih.tail ⟨(hadj _ _).mpr ⟨_, _, rfl, rfl, h.1⟩, h.2⟩
      exact F.2.2.1 (emb u) (hlift u u hu), by
      have himg : ∀ {P : M → M → Prop} {P' : W → W → Prop},
          (∀ p q, P p q ↔ ∃ u v, p = emb u ∧ q = emb v ∧ P' u v) →
          {p : M × M | P p.1 p.2}.ncard = {p : W × W | P' p.1 p.2}.ncard := by
        intro P P' hP
        have hset : {p : M × M | P p.1 p.2} = Prod.map emb emb '' {p : W × W | P' p.1 p.2} := by
          ext p
          constructor
          · intro hp
            obtain ⟨u, v, hu, hv, h⟩ := (hP _ _).mp hp
            exact ⟨(u, v), h, Prod.ext hu.symm hv.symm⟩
          · rintro ⟨⟨u, v⟩, h, rfl⟩
            exact (hP _ _).mpr ⟨u, v, rfl, rfl, h⟩
        rw [hset, Set.ncard_image_of_injective _ (hinj.prodMap hinj)]
      have h₁ := himg (P := F.1) (P' := fun u v => F.1 (emb u) (emb v)) fun p q =>
        ⟨fun h => by
          obtain ⟨u, v, hu, hv, -⟩ := (hadj _ _).mp (F.2.1 _ _ h)
          exact ⟨u, v, hu, hv, hu ▸ hv ▸ h⟩, fun ⟨u, v, hu, hv, h⟩ => hu ▸ hv ▸ h⟩
      exact h₁.symm.trans (F.2.2.2.trans (himg hK))⟩
  invFun F := ⟨fun p q => ∃ u v, p = emb u ∧ q = emb v ∧ F.1 u v,
    fun p q ⟨u, v, hu, hv, h⟩ => (hadj _ _).mpr ⟨u, v, hu, hv, F.2.1 _ _ h⟩, fun p hp => by
      have hlift : ∀ a b, Relation.TransGen
          (UncutArc AdjM fun p q => ∃ u v, p = emb u ∧ q = emb v ∧ F.1 u v) a b →
          ∃ u v, a = emb u ∧ b = emb v ∧ Relation.TransGen (UncutArc AdjW F.1) u v := by
        intro a b hab
        induction hab with
        | single h =>
          obtain ⟨u, v, hu, hv, h'⟩ := (hadj _ _).mp h.1
          exact ⟨u, v, hu, hv, .single ⟨h', fun hF => h.2 ⟨u, v, hu, hv, hF⟩⟩⟩
        | tail _ h ih =>
          obtain ⟨u, v, hu, hv, hT⟩ := ih
          obtain ⟨v', w, hv', hw, h'⟩ := (hadj _ _).mp h.1
          have hvv : v = v' := hinj (hv.symm.trans hv')
          subst hvv
          exact ⟨u, w, hu, hw, hT.tail ⟨h', fun hF => h.2 ⟨v, w, hv, hw, hF⟩⟩⟩
      obtain ⟨u, v, hu, hv, hT⟩ := hlift p p hp
      have huv : u = v := hinj (hu.symm.trans hv)
      subst huv
      exact F.2.2.1 u hT, by
      have himg : ∀ {P : M → M → Prop} {P' : W → W → Prop},
          (∀ p q, P p q ↔ ∃ u v, p = emb u ∧ q = emb v ∧ P' u v) →
          {p : M × M | P p.1 p.2}.ncard = {p : W × W | P' p.1 p.2}.ncard := by
        intro P P' hP
        have hset : {p : M × M | P p.1 p.2} = Prod.map emb emb '' {p : W × W | P' p.1 p.2} := by
          ext p
          constructor
          · intro hp
            obtain ⟨u, v, hu, hv, h⟩ := (hP _ _).mp hp
            exact ⟨(u, v), h, Prod.ext hu.symm hv.symm⟩
          · rintro ⟨⟨u, v⟩, h, rfl⟩
            exact (hP _ _).mpr ⟨u, v, rfl, rfl, h⟩
        rw [hset, Set.ncard_image_of_injective _ (hinj.prodMap hinj)]
      exact (himg fun _ _ => Iff.rfl).trans (F.2.2.2.trans (himg hK).symm)⟩
  left_inv F := Subtype.ext (funext fun p => funext fun q => propext
    ⟨fun ⟨u, v, hu, hv, h⟩ => by
      have h' : F.1 (emb u) (emb v) := h
      rw [hu, hv]
      exact h', fun h => by
      obtain ⟨u, v, hu, hv, -⟩ := (hadj _ _).mp (F.2.1 _ _ h)
      refine ⟨u, v, hu, hv, ?_⟩
      change F.1 (emb u) (emb v)
      rw [← hu, ← hv]
      exact h⟩)
  right_inv F := Subtype.ext (funext fun u => funext fun v => propext
    ⟨fun ⟨u', v', hu, hv, h⟩ => by
      rw [hinj hu, hinj hv]
      exact h, fun h => ⟨u, v, rfl, rfl, h⟩⟩)

end Embedding

/-! ### The interpretation -/

namespace CliqueFas

open SplitBundle

/-- Tags of the interpretation: the kinds of vertices of the conflict split
graph. -/
inductive SBTag : Type
  /-- The entry copy of a vertex, at diagonal pairs. -/
  | vin
  /-- The exit copy of a vertex, at diagonal pairs. -/
  | vout
  /-- The middle of one of the two paths from the first component to the
  second. -/
  | mid (j : Bool)
  deriving DecidableEq

instance : Finite SBTag := by
  let enc : SBTag → Fin 3 × Bool := fun t =>
    match t with
    | .vin => (0, false)
    | .vout => (1, false)
    | .mid j => (2, j)
  refine Finite.of_injective enc fun u v h => ?_
  cases u <;> cases v <;> simp_all [enc]

instance : Nonempty SBTag := ⟨.vin⟩

section Formulas

variable {α : Type}

/-- `x` and `y` are adjacent, as a formula. -/
def adjF (x y : α) : Language.markedGraph.Formula α :=
  Relations.formula₂ mgAdj (Term.var x) (Term.var y)

/-- `x = y`, as a formula. -/
def eqF (x y : α) : Language.markedGraph.Formula α := Term.equal (Term.var x) (Term.var y)

/-- Some vertex is marked, as a formula. -/
noncomputable def gateF : Language.markedGraph.Formula α :=
  (Relations.formula₁ mgMarked (Term.var (Sum.inr ()))).iExs Unit

/-- `x` and `y` are in conflict, as a formula. -/
def confF (x y : α) : Language.markedGraph.Formula α :=
  ∼(eqF x y) ⊓ (∼(adjF x y) ⊔ ∼(adjF y x))

/-- The arc formulas of the conflict split graph, by tags. The free variable
`(i, j)` is the `j`-th component of the `i`-th vertex. -/
noncomputable def arcF : SBTag → SBTag → Language.markedGraph.Formula (Fin 2 × Fin 2)
  | .vin, .vout => gateF ⊓ (eqF (0, 0) (0, 1) ⊓ (eqF (1, 0) (1, 1) ⊓ eqF (0, 0) (1, 0)))
  | .vout, .mid _ => gateF ⊓ (eqF (0, 0) (0, 1) ⊓ (eqF (0, 0) (1, 0) ⊓ confF (1, 0) (1, 1)))
  | .mid _, .vin => gateF ⊓ (eqF (1, 0) (1, 1) ⊓ (eqF (0, 1) (1, 0) ⊓ confF (0, 0) (0, 1)))
  | _, _ => ⊥

/-- The mark formulas, by tags: the internal arcs of the unmarked vertices. -/
noncomputable def markF : SBTag → SBTag → Language.markedGraph.Formula (Fin 2 × Fin 2)
  | .vin, .vout =>
      gateF ⊓ (eqF (0, 0) (0, 1) ⊓ (eqF (1, 0) (1, 1) ⊓ (eqF (0, 0) (1, 0) ⊓
        ∼(Relations.formula₁ mgMarked (Term.var (0, 0))))))
  | _, _ => ⊥

end Formulas

/-- The interpretation drawing the conflict split graph of a marked graph. -/
noncomputable def cliqueFasInterp :
    FOInterpretation Language.markedGraph Language.markedArcGraph SBTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .adj => fun t => arcF (t 0) (t 1)
    | _, .marked => fun t => markF (t 0) (t 1)

section Realize

variable {H : Type} [Language.markedGraph.Structure H]

/-- The arc condition of the interpretation, on tags and coordinates. -/
def ArcCore : SBTag → H → H → SBTag → H → H → Prop
  | .vin, x, y, .vout, x', y' => (∃ z : H, MGMarked z) ∧ x = y ∧ x' = y' ∧ x = x'
  | .vout, x, y, .mid _, x', y' =>
      (∃ z : H, MGMarked z) ∧ x = y ∧ x = x' ∧ Conf (fun a b : H => MGAdj a b) x' y'
  | .mid _, x, y, .vin, x', y' =>
      (∃ z : H, MGMarked z) ∧ x' = y' ∧ y = x' ∧ Conf (fun a b : H => MGAdj a b) x y
  | _, _, _, _, _, _ => False

/-- The mark condition of the interpretation, on tags and coordinates. -/
def MarkCore : SBTag → H → H → SBTag → H → H → Prop
  | .vin, x, y, .vout, x', y' =>
      (∃ z : H, MGMarked z) ∧ x = y ∧ x' = y' ∧ x = x' ∧ ¬MGMarked x
  | _, _, _, _, _, _ => False

variable {α : Type} {v : α → H}

theorem realize_adjF {x y : α} : (adjF x y).Realize v ↔ MGAdj (v x) (v y) := by
  rw [adjF, Formula.realize_rel₂]
  exact Iff.rfl

theorem realize_eqF {x y : α} : (eqF x y).Realize v ↔ v x = v y := by
  simp [eqF]

theorem realize_gateF : (gateF (α := α)).Realize v ↔ ∃ z : H, MGMarked z := by
  simp only [gateF, Formula.realize_iExs, Formula.realize_rel₁, Term.realize_var, Sum.elim_inr]
  exact ⟨fun ⟨i, h⟩ => ⟨i (), h⟩, fun ⟨z, h⟩ => ⟨fun _ => z, h⟩⟩

theorem realize_confF {x y : α} :
    (confF x y).Realize v ↔ Conf (fun a b : H => MGAdj a b) (v x) (v y) := by
  simp [confF, Conf, realize_eqF, realize_adjF]

theorem realize_arcF {t t' : SBTag} {v : Fin 2 × Fin 2 → H} :
    (arcF t t').Realize v ↔ ArcCore t (v (0, 0)) (v (0, 1)) t' (v (1, 0)) (v (1, 1)) := by
  cases t <;> cases t' <;>
    simp [arcF, ArcCore, realize_gateF, realize_eqF, realize_confF]

theorem realize_markF {t t' : SBTag} {v : Fin 2 × Fin 2 → H} :
    (markF t t').Realize v ↔ MarkCore t (v (0, 0)) (v (0, 1)) t' (v (1, 0)) (v (1, 1)) := by
  cases t <;> cases t' <;>
    simp [markF, MarkCore, realize_gateF, realize_eqF, Formula.realize_rel₁, MGMarked]

end Realize

/-! ### The interpreted graph is the conflict split graph, plus isolated points -/

section Points

variable {H : Type}

/-- The point of tag `t` at the pair `(x, y)`. -/
def fpt (t : SBTag) (x y : H) : cliqueFasInterp.Map H := (t, ![x, y])

theorem eq_fpt (p : cliqueFasInterp.Map H) : p = fpt p.1 (p.2 0) (p.2 1) := by
  obtain ⟨t, w⟩ := p
  refine Prod.ext_iff.mpr ⟨rfl, funext fun j => ?_⟩
  fin_cases j <;> rfl

theorem fpt_inj {t t' : SBTag} {x y x' y' : H} (h : fpt t x y = fpt t' x' y') :
    t = t' ∧ x = x' ∧ y = y' :=
  ⟨congrArg (fun p : cliqueFasInterp.Map H => p.1) h,
    congrArg (fun p : cliqueFasInterp.Map H => p.2 0) h,
    congrArg (fun p : cliqueFasInterp.Map H => p.2 1) h⟩

/-- A vertex of the conflict split graph, as a point of the interpretation. -/
def emb : SB H → cliqueFasInterp.Map H
  | .vin a => fpt .vin a a
  | .vout a => fpt .vout a a
  | .mid j a b => fpt (.mid j) a b

theorem emb_injective : Function.Injective (emb (H := H)) := by
  intro u v h
  cases u <;> cases v <;> obtain ⟨ht, h₀, h₁⟩ := fpt_inj h <;>
    first
      | (cases ht; done)
      | (cases ht; rw [h₀, h₁])
      | rw [h₀]

end Points

section Characterization

variable {H : Type} [Language.markedGraph.Structure H]

theorem arcCore_iff (t t' : SBTag) (x y x' y' : H) :
    ArcCore t x y t' x' y' ↔ ∃ u v, fpt t x y = emb u ∧ fpt t' x' y' = emb v ∧
      SArc (fun a b : H => MGAdj a b) (fun a => MGMarked a) u v := by
  constructor
  · intro h
    cases t <;> cases t' <;> try exact (h : False).elim
    · obtain ⟨hg, hxy, hxy', hxx⟩ := h
      subst hxy hxy' hxx
      exact ⟨.vin x, .vout x, rfl, rfl, hg, rfl⟩
    · rename_i j
      obtain ⟨hg, hxy, hxx, hc⟩ := h
      subst hxy hxx
      exact ⟨.vout x, .mid j x y', rfl, rfl, hg, rfl, hc⟩
    · rename_i j
      obtain ⟨hg, hxy', hyx, hc⟩ := h
      subst hxy' hyx
      exact ⟨.mid j x y, .vin y, rfl, rfl, hg, rfl, hc⟩
  · rintro ⟨u, v, hu, hv, h⟩
    cases u <;> cases v <;> try exact (h : False).elim
    · obtain ⟨ht, hx, hy⟩ := fpt_inj hu
      obtain ⟨ht', hx', hy'⟩ := fpt_inj hv
      obtain ⟨hg, hab⟩ := h
      subst ht ht' hx hy hx' hy' hab
      exact ⟨hg, rfl, rfl, rfl⟩
    · obtain ⟨ht, hx, hy⟩ := fpt_inj hu
      obtain ⟨ht', hx', hy'⟩ := fpt_inj hv
      obtain ⟨hg, hab, hc⟩ := h
      subst ht ht' hx hy hx' hy' hab
      exact ⟨hg, rfl, rfl, hc⟩
    · obtain ⟨ht, hx, hy⟩ := fpt_inj hu
      obtain ⟨ht', hx', hy'⟩ := fpt_inj hv
      obtain ⟨hg, hab, hc⟩ := h
      subst ht ht' hx hy hx' hy' hab
      exact ⟨hg, rfl, rfl, hc⟩

theorem markCore_iff (t t' : SBTag) (x y x' y' : H) :
    MarkCore t x y t' x' y' ↔ ∃ u v, fpt t x y = emb u ∧ fpt t' x' y' = emb v ∧
      SMark (fun a : H => MGMarked a) u v := by
  constructor
  · intro h
    cases t <;> cases t' <;> try exact (h : False).elim
    obtain ⟨hg, hxy, hxy', hxx, hm⟩ := h
    subst hxy hxy' hxx
    exact ⟨.vin x, .vout x, rfl, rfl, hg, rfl, hm⟩
  · rintro ⟨u, v, hu, hv, h⟩
    cases u <;> cases v <;> try exact (h : False).elim
    obtain ⟨ht, hx, hy⟩ := fpt_inj hu
    obtain ⟨ht', hx', hy'⟩ := fpt_inj hv
    obtain ⟨hg, hab, hm⟩ := h
    subst ht ht' hx hy hx' hy' hab
    exact ⟨hg, rfl, rfl, rfl, hm⟩

theorem interp_adj (t t' : SBTag) (w w' : Fin 2 → H) :
    RelMap (M := cliqueFasInterp.Map H) magAdj ![(t, w), (t', w')] ↔
      ArcCore t (w 0) (w 1) t' (w' 0) (w' 1) := by
  rw [FOInterpretation.relMap_map]
  exact realize_arcF

theorem interp_marked (t t' : SBTag) (w w' : Fin 2 → H) :
    RelMap (M := cliqueFasInterp.Map H) magMarked ![(t, w), (t', w')] ↔
      MarkCore t (w 0) (w 1) t' (w' 0) (w' 1) := by
  rw [FOInterpretation.relMap_map]
  exact realize_markF

theorem magAdj_iff (p q : cliqueFasInterp.Map H) :
    MAGAdj p q ↔ ∃ u v, p = emb u ∧ q = emb v ∧
      SArc (fun a b : H => MGAdj a b) (fun a => MGMarked a) u v := by
  have h : MAGAdj p q ↔ ArcCore p.1 (p.2 0) (p.2 1) q.1 (q.2 0) (q.2 1) := by
    obtain ⟨t, w⟩ := p
    obtain ⟨t', w'⟩ := q
    exact interp_adj t t' w w'
  rw [h, arcCore_iff, ← eq_fpt p, ← eq_fpt q]

theorem magMarked_iff (p q : cliqueFasInterp.Map H) :
    MAGMarked p q ↔ ∃ u v, p = emb u ∧ q = emb v ∧ SMark (fun a : H => MGMarked a) u v := by
  have h : MAGMarked p q ↔ MarkCore p.1 (p.2 0) (p.2 1) q.1 (q.2 0) (q.2 1) := by
    obtain ⟨t, w⟩ := p
    obtain ⟨t', w'⟩ := q
    exact interp_marked t t' w w'
  rw [h, markCore_iff, ← eq_fpt p, ← eq_fpt q]

variable (H) [Finite H]

/-- **Correctness of the interpretation, under the promise**: on a marked graph
with no marked vertex, or with no clique larger than its marked set, the
feedback arc sets of the threshold size of the conflict split graph are as
many as the cliques of the threshold size. -/
theorem sharpFeedbackArcSet_cliqueFas
    (hprom : (¬∃ z : H, MGMarked z) ∨ ∀ S : H → Prop,
      (∀ x y, S x → S y → x ≠ y → MGAdj x y) → {x | S x}.ncard ≤ {x : H | MGMarked x}.ncard) :
    SharpFeedbackArcSet (cliqueFasInterp.Map H) = SharpClique H := by
  have hM := cliqueFasInterp.map_finite H
  rw [sharpFeedbackArcSet_apply, sharpClique_apply]
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_iff_right hM)).trans ?_
  refine (Nat.card_congr (fasOfSizeOnEmbEquiv emb emb_injective magAdj_iff magMarked_iff)).trans ?_
  refine (card_fas_eq_card_clique (fun a b : H => MGAdj a b) (fun a => MGMarked a) hprom).trans ?_
  exact (Nat.card_congr (Equiv.subtypeEquivRight fun _ => and_iff_right ‹Finite H›)).symm

end Characterization

end CliqueFas

/-! ### The promise, and a composition under it -/

namespace OneInToClique

open SatOcc

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A]

/-- **The clique instance of a CNF formula has no clique larger than its marked
set**, as soon as it has a marked vertex: a clique with two vertices fills
distinct slots, and one vertex is no more than two per clause. -/
theorem ncard_clique_le (hne : ∃ p : oneInToClique.Map A, MGMarked p)
    {S : oneInToClique.Map A → Prop}
    (hS : ∀ p q : oneInToClique.Map A, S p → S q → p ≠ q → MGAdj p q) :
    {p | S p}.ncard ≤ {p : oneInToClique.Map A | MGMarked p}.ncard := by
  have := oneInToClique.map_finite A
  rw [ncard_marked]
  obtain ⟨p₀, hp₀⟩ := hne
  have hcl : ∃ c : A, IsCl c := by
    have h := (marked_iff p₀).mp hp₀
    revert h
    generalize p₀.1 = t
    intro h
    cases t
    exacts [⟨_, h.2⟩, h.elim, ⟨_, h.2⟩]
  obtain ⟨c, hc⟩ := hcl
  have : Nonempty (Slot A) := ⟨Sum.inl ⟨c, hc⟩⟩
  have hslot : 0 < Nat.card (Slot A) := Nat.card_pos
  by_cases h2 : 1 < {p | S p}.ncard
  · have hv : ∀ p : oneInToClique.Map A, S p → Valid p.1 (p.2 0) (p.2 1) := fun p hp => by
      obtain ⟨q, hq, hqp⟩ := Set.exists_ne_of_one_lt_ncard h2 p
      exact ((adj_iff p q).mp (hS p q hp hq (Ne.symm hqp))).1
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_injective (slot hv) (slot_injective hS hv)
  · omega

end OneInToClique

section Promise

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]

/-- An order-free interpretation, over the ordered expansion: its formulas
ignore the order. -/
def FOInterpretation.liftOrd {Tag : Type} {d : ℕ} (f : FOInterpretation L₂ L₃ Tag d) :
    FOInterpretation (L₂.sum Language.order) L₃ Tag d where
  relFormula := fun R t => LHom.sumInl.onFormula (f.relFormula R t)

/-- Lifting an interpretation to the ordered expansion does not change the
structure it defines. -/
def FOInterpretation.liftOrdLEquiv {Tag : Type} {d : ℕ} (f : FOInterpretation L₂ L₃ Tag d)
    (A : Type) [L₂.Structure A] [LinearOrder A] : f.Map A ≃[L₃] f.liftOrd.Map A where
  toEquiv := Equiv.refl _
  map_fun' := fun f => isEmptyElim f
  map_rel' := fun {n} R x => by
    rw [FOInterpretation.relMap_map, FOInterpretation.relMap_map]
    exact LHom.realize_onFormula _ _

variable {C : CountingProblem L₁} {D : CountingProblem L₂} {E : CountingProblem L₃}

/-- **Composition under a promise**: an ordered parsimonious reduction followed
by an interpretation that is only known to preserve the count *on the outputs
of the reduction*. This is what a reduction through instances with no slack
needs, the second step being wrong on the others. -/
noncomputable def OrderedParsimoniousReduction.transPromise (g : C ≤ᵖ[≤] D) {Tag : Type}
    [Finite Tag] [Nonempty Tag] {d : ℕ} (f : FOInterpretation L₂ L₃ Tag d)
    (hf : ∀ (A : Type) [L₁.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      D (g.toInterpretation.Map A) = E (f.Map (g.toInterpretation.Map A))) : C ≤ᵖ[≤] E :=
  letI := g.tagFinite
  letI := g.tagNonempty
  letI : LinearOrder g.Tag := finiteLinearOrder g.Tag
  { Tag := Tag × (Fin d → g.Tag)
    dim := d * g.dim
    toInterpretation := f.liftOrd.comp g.toInterpretation.ordExtend
    correct := fun A _ _ _ _ => by
      let := g.toInterpretation.mapLinearOrder A
      have : Finite (g.toInterpretation.Map A) := g.toInterpretation.map_finite A
      have : Nonempty (g.toInterpretation.Map A) := g.toInterpretation.map_nonempty A
      have h1 := g.correct A
      have h2 := hf A
      have e0 := f.liftOrdLEquiv (g.toInterpretation.Map A)
      have e1 := g.toInterpretation.ordExtendLEquiv A
      have e2 := f.liftOrd.mapLEquiv e1
      have e3 := f.liftOrd.compLEquiv g.toInterpretation.ordExtend A
      exact (h1.trans h2).trans
        ((E.iso_invariant e0).trans (E.iso_invariant (e2.comp e3)).symm) }

end Promise

/-- **#1-in-SAT reduces parsimoniously to #Feedback Arc Set**: the clique
instance of the formula, then its conflict split graph. -/
noncomputable def sharpOneInSat_ordered_parsimonious_sharpFeedbackArcSet :
    SharpOneInSAT ≤ᵖ[≤] SharpFeedbackArcSet :=
  sharpOneInSat_ordered_parsimonious_sharpClique.transPromise CliqueFas.cliqueFasInterp
    fun A _ _ _ _ => by
      have := OneInToClique.oneInToClique.map_finite A
      refine (CliqueFas.sharpFeedbackArcSet_cliqueFas (OneInToClique.oneInToClique.Map A) ?_).symm
      by_cases hne : ∃ z : OneInToClique.oneInToClique.Map A, MGMarked z
      · exact Or.inr fun S hS => OneInToClique.ncard_clique_le hne hS
      · exact Or.inl hne

/-- #Feedback Arc Set is parsimoniously `#P`-hard. -/
theorem sharpFeedbackArcSet_sharpP_parsimoniousHard :
    SharpP.ParsimoniousHard SharpFeedbackArcSet :=
  SharpP.parsimoniousHard_of_orderedParsimonious
    sharpOneInSat_ordered_parsimonious_sharpFeedbackArcSet sharpOneInSat_sharpP_parsimoniousHard

/-- **#Feedback Arc Set is parsimoniously `#P`-complete**, counting the
feedback arc sets of exactly the threshold size.
Registered in the Lax archive as
[`Lax280166.FeedbackArcSetComplete.sharpFeedbackArcSet_sharpP_parsimoniousComplete`](https://laxarchive.org/lax-280166/Lax280166.FeedbackArcSetComplete.html#s-Lax280166.FeedbackArcSetComplete.sharpFeedbackArcSet_sharpP_parsimoniousComplete). -/
theorem sharpFeedbackArcSet_sharpP_parsimoniousComplete :
    SharpP.ParsimoniousComplete SharpFeedbackArcSet :=
  ⟨sharpFeedbackArcSet_mem_sharpP, sharpFeedbackArcSet_sharpP_parsimoniousHard⟩

/-- `SharpFeedbackArcSet` is `#P`-complete: parsimoniously, hence under subtractive
reductions. -/
theorem sharpFeedbackArcSet_sharpP_complete : SharpP.Complete SharpFeedbackArcSet :=
  complete_sharpP_of_parsimoniousComplete sharpFeedbackArcSet_sharpP_parsimoniousComplete

end DescriptiveComplexity
