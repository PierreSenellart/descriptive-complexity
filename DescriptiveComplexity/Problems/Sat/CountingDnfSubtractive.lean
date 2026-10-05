/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Sat.CountingDnf
import DescriptiveComplexity.Counting.Subtractive

/-!
# #DNF is `#P`-complete

The reduction of #SAT to #DNF, as the strong subtractive reduction it is in
[Durand, Hermann, Kolaitis 2005][durand2005subtractive] (Proposition 3.4): the
number of models of a CNF formula is the number of models of a tautology over
its variables, minus the number of models of its negation, and the models of
the negation are models of the tautology.
`DescriptiveComplexity.Problems.Sat.CountingDnf` has the same reduction with one
oracle call, the count at the tautology being known; here both instances are
drawn, and the statement is the stronger one, since `#P` is closed under
subtractive reductions
(`DescriptiveComplexity.sharpDnf_sharpP_complete`).

The two instances have to share their universe, and a tautology over `n`
variables needs `n + 1` terms when every element is a variable, so the universe
is doubled:

* `DescriptiveComplexity.dnfSubInterp`, the subtrahend, carries the sign swap
  of the formula on one tag and nothing on the other;
* `DescriptiveComplexity.dnfMinInterp`, the minuend, has the term `x` on one
  tag and the term `¬x` on the other for each variable `x`, and an empty term
  for each element that is not a variable.

The semantic content is two lemmas about a formula embedded in a larger
universe, `DescriptiveComplexity.dnfModel_embed_swap_iff` (De Morgan) and
`DescriptiveComplexity.card_embedded_sets`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Formulas embedded in a larger universe -/

section Embed

variable {A B : Type} [Language.sat.Structure A] [Language.sat.Structure B]

/-- **De Morgan's law, for an embedded formula**: if `B` carries, on the image
of `ι`, the sign swap of the CNF formula `A`, and nothing elsewhere, then the
models of `B` read as a DNF formula are the sets of images of variables of `A`
that are not models of `A`. -/
theorem dnfModel_embed_swap_iff {ι : A → B} (hι : Function.Injective ι)
    (hcl : ∀ y : B, RelMap satIsClause ![y] ↔ ∃ c, y = ι c ∧ RelMap satIsClause ![c])
    (hpos : ∀ y z : B, RelMap satPosIn ![y, z] ↔
      ∃ c x, y = ι c ∧ z = ι x ∧ RelMap satNegIn ![c, x])
    (hneg : ∀ y z : B, RelMap satNegIn ![y, z] ↔
      ∃ c x, y = ι c ∧ z = ι x ∧ RelMap satPosIn ![c, x])
    (μ : B → Prop) :
    DnfModel B μ ↔
      (∀ y, μ y → ∃ a, y = ι a ∧ SatOccurs A a) ∧ ¬SatModel A fun a => μ (ι a) := by
  have hocc : ∀ y : B, SatOccurs B y ↔ ∃ a, y = ι a ∧ SatOccurs A a := by
    intro y
    constructor
    · rintro ⟨d, hd, h⟩
      obtain ⟨c₀, hd₀, hc₀⟩ := (hcl d).mp hd
      rcases h with h | h
      · obtain ⟨c, x, hc, hx, hn⟩ := (hpos d y).mp h
        have hcc : c₀ = c := hι (hd₀.symm.trans hc)
        exact ⟨x, hx, c, hcc ▸ hc₀, Or.inr hn⟩
      · obtain ⟨c, x, hc, hx, hp⟩ := (hneg d y).mp h
        have hcc : c₀ = c := hι (hd₀.symm.trans hc)
        exact ⟨x, hx, c, hcc ▸ hc₀, Or.inl hp⟩
    · rintro ⟨a, rfl, c, hc, h⟩
      exact ⟨ι c, (hcl _).mpr ⟨c, rfl, hc⟩,
        h.symm.imp (fun hn => (hpos _ _).mpr ⟨c, a, rfl, rfl, hn⟩)
          fun hp => (hneg _ _).mpr ⟨c, a, rfl, rfl, hp⟩⟩
  constructor
  · rintro ⟨⟨d, hd, hall⟩, hsub⟩
    refine ⟨fun y hy => (hocc y).mp (hsub y hy), fun hm => ?_⟩
    obtain ⟨c, hdc, hc⟩ := (hcl d).mp hd
    obtain ⟨x, ⟨hp, hx⟩ | ⟨hn, hx⟩⟩ := hm.1 c hc
    · exact (hall (ι x)).2 ((hneg _ _).mpr ⟨c, x, hdc, rfl, hp⟩) hx
    · exact hx ((hall (ι x)).1 ((hpos _ _).mpr ⟨c, x, hdc, rfl, hn⟩))
  · rintro ⟨hsupp, hnm⟩
    have hsubA : ∀ a, μ (ι a) → SatOccurs A a := by
      intro a ha
      obtain ⟨a', e, ho⟩ := hsupp _ ha
      exact hι e ▸ ho
    have hno : ¬∀ c : A, RelMap satIsClause ![c] →
        ∃ x : A, (RelMap satPosIn ![c, x] ∧ μ (ι x)) ∨ (RelMap satNegIn ![c, x] ∧ ¬μ (ι x)) :=
      fun h => hnm ⟨h, hsubA⟩
    obtain ⟨c, hc⟩ := not_forall.mp hno
    obtain ⟨hc, hx⟩ := Classical.not_imp.mp hc
    have hx' := not_exists.mp hx
    refine ⟨⟨ι c, (hcl _).mpr ⟨c, rfl, hc⟩, fun z => ⟨fun hp => ?_, fun hn hz => ?_⟩⟩,
      fun y hy => (hocc y).mpr (hsupp y hy)⟩
    · obtain ⟨c', x, e, hzx, hn⟩ := (hpos _ _).mp hp
      have hcc : c = c' := hι e
      subst hcc
      subst hzx
      by_contra hz
      exact hx' x (Or.inr ⟨hn, hz⟩)
    · obtain ⟨c', x, e, hzx, hp⟩ := (hneg _ _).mp hn
      have hcc : c = c' := hι e
      subst hcc
      subst hzx
      exact hx' x (Or.inl ⟨hp, hz⟩)

omit [Language.sat.Structure A] [Language.sat.Structure B] in
/-- Sets of images of elements satisfying `p`, with a condition on their
preimage, are as many as the sets of elements satisfying `p` with that
condition. -/
theorem card_embedded_sets {ι : A → B} (hι : Function.Injective ι) (p : A → Prop)
    (R : (A → Prop) → Prop) :
    Nat.card {μ : B → Prop // (∀ y, μ y → ∃ a, y = ι a ∧ p a) ∧ R fun a => μ (ι a)} =
      Nat.card {ν : A → Prop // (∀ a, ν a → p a) ∧ R ν} := by
  have hback : ∀ ν : A → Prop, (fun a => ∃ a', ι a = ι a' ∧ ν a') = ν := fun ν =>
    funext fun a => propext ⟨fun ⟨a', e, h⟩ => hι e ▸ h, fun h => ⟨a, rfl, h⟩⟩
  exact Nat.card_congr
    { toFun := fun μ => ⟨fun a => μ.1 (ι a), fun a ha => by
        obtain ⟨a', e, ho⟩ := μ.2.1 _ ha
        exact hι e ▸ ho, μ.2.2⟩
      invFun := fun ν => ⟨fun y => ∃ a, y = ι a ∧ ν.1 a,
        fun y ⟨a, e, h⟩ => ⟨a, e, ν.2.1 a h⟩, (hback ν.1).symm ▸ ν.2.2⟩
      left_inv := fun μ => Subtype.ext (funext fun y => propext
        ⟨fun ⟨a, e, h⟩ => (congrArg μ.1 e).mpr h, fun h => by
          obtain ⟨a, e, _⟩ := μ.2.1 y h
          exact ⟨a, e, (congrArg μ.1 e).mp h⟩⟩)
      right_inv := fun ν => Subtype.ext (hback ν.1) }

end Embed

/-! ### The two instances -/

/-- The subtrahend: the sign swap of the formula on the tag `false`, and
nothing on the tag `true`. -/
noncomputable def dnfSubInterp :
    FOInterpretation (Language.sat.sum Language.order) Language.sat Bool 1 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun t =>
      match t 0 with
      | false => LHom.sumInl.onFormula (fo%⟨c⟩ satIsClause(c))
      | true => ⊥
    | _, .posIn => fun t =>
      match t 0, t 1 with
      | false, false => LHom.sumInl.onFormula (fo%⟨c, x⟩ satNegIn(c, x))
      | _, _ => ⊥
    | _, .negIn => fun t =>
      match t 0, t 1 with
      | false, false => LHom.sumInl.onFormula (fo%⟨c, x⟩ satPosIn(c, x))
      | _, _ => ⊥

/-- The minuend: a tautology over the same variables. Each variable `x` gives
the term `x` on the tag `false` and the term `¬x` on the tag `true`, and an
element that is not a variable gives the empty term on the tag `true`. -/
noncomputable def dnfMinInterp :
    FOInterpretation (Language.sat.sum Language.order) Language.sat Bool 1 where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun t =>
      match t 0 with
      | false => LHom.sumInl.onFormula (fo%⟨c⟩ satOccursAt⟨c⟩)
      | true => ⊤
    | _, .posIn => fun t =>
      match t 0, t 1 with
      | false, false => LHom.sumInl.onFormula (fo%⟨c, x⟩ (c ≐ x) ∧ satOccursAt⟨c⟩)
      | _, _ => ⊥
    | _, .negIn => fun t =>
      match t 0, t 1 with
      | true, false => LHom.sumInl.onFormula (fo%⟨c, x⟩ (c ≐ x) ∧ satOccursAt⟨c⟩)
      | _, _ => ⊥

section Instances

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

theorem dnfSub_isClause (b : Bool) (w : Fin 1 → A) :
    RelMap (M := dnfSubInterp.Map A) satIsClause ![(b, w)] ↔
      b = false ∧ RelMap satIsClause ![w 0] := by
  rw [FOInterpretation.relMap_map]
  cases b <;> simp [dnfSubInterp, LHom.realize_onFormula, Formula.realize_rel₁]

theorem dnfSub_posIn (b b' : Bool) (w w' : Fin 1 → A) :
    RelMap (M := dnfSubInterp.Map A) satPosIn ![(b, w), (b', w')] ↔
      b = false ∧ b' = false ∧ RelMap satNegIn ![w 0, w' 0] := by
  rw [FOInterpretation.relMap_map]
  cases b <;> cases b' <;>
    simp [dnfSubInterp, LHom.realize_onFormula, Formula.realize_rel₂]

theorem dnfSub_negIn (b b' : Bool) (w w' : Fin 1 → A) :
    RelMap (M := dnfSubInterp.Map A) satNegIn ![(b, w), (b', w')] ↔
      b = false ∧ b' = false ∧ RelMap satPosIn ![w 0, w' 0] := by
  rw [FOInterpretation.relMap_map]
  cases b <;> cases b' <;>
    simp [dnfSubInterp, LHom.realize_onFormula, Formula.realize_rel₂]

theorem dnfMin_isClause (b : Bool) (w : Fin 1 → A) :
    RelMap (M := dnfMinInterp.Map A) satIsClause ![(b, w)] ↔
      b = true ∨ SatOccurs A (w 0) := by
  rw [FOInterpretation.relMap_map]
  cases b <;> simp [dnfMinInterp, LHom.realize_onFormula, realize_satOccursAt]

theorem dnfMin_posIn (b b' : Bool) (w w' : Fin 1 → A) :
    RelMap (M := dnfMinInterp.Map A) satPosIn ![(b, w), (b', w')] ↔
      b = false ∧ b' = false ∧ w 0 = w' 0 ∧ SatOccurs A (w 0) := by
  rw [FOInterpretation.relMap_map]
  cases b <;> cases b' <;>
    simp [dnfMinInterp, LHom.realize_onFormula, realize_satOccursAt]

theorem dnfMin_negIn (b b' : Bool) (w w' : Fin 1 → A) :
    RelMap (M := dnfMinInterp.Map A) satNegIn ![(b, w), (b', w')] ↔
      b = true ∧ b' = false ∧ w 0 = w' 0 ∧ SatOccurs A (w 0) := by
  rw [FOInterpretation.relMap_map]
  cases b <;> cases b' <;>
    simp [dnfMinInterp, LHom.realize_onFormula, realize_satOccursAt]

/-- The image of an element of the formula in the two instances: the point
of tag `false`. -/
def dnfPt (a : A) : Bool × (Fin 1 → A) := (false, fun _ => a)

omit [Language.sat.Structure A] [LinearOrder A] in
theorem dnfPt_injective : Function.Injective (dnfPt (A := A)) := fun _ _ h =>
  congrFun (Prod.mk.inj h).2 0

omit [Language.sat.Structure A] [LinearOrder A] in
theorem eq_dnfPt (z : Bool × (Fin 1 → A)) {a : A} (h1 : z.1 = false) (h2 : a = z.2 0) :
    z = dnfPt a :=
  Prod.ext h1 (funext fun j => by rw [h2]; exact congrArg z.2 (Subsingleton.elim j 0))

/-- The models of the subtrahend are the sets of images of variables of the
formula that are not models of it. -/
theorem dnfSub_model_iff (μ : dnfSubInterp.Map A → Prop) :
    DnfModel (dnfSubInterp.Map A) μ ↔
      (∀ y, μ y → ∃ a, y = dnfPt a ∧ SatOccurs A a) ∧ ¬SatModel A fun a => μ (dnfPt a) := by
  refine dnfModel_embed_swap_iff (B := dnfSubInterp.Map A) (ι := dnfPt) dnfPt_injective
    (fun y => ?_) (fun y z => ?_) (fun y z => ?_) μ
  · refine (dnfSub_isClause y.1 y.2).trans ⟨fun h => ⟨y.2 0, eq_dnfPt y h.1 rfl, h.2⟩, ?_⟩
    rintro ⟨c, rfl, hc⟩
    exact ⟨rfl, hc⟩
  · refine (dnfSub_posIn y.1 z.1 y.2 z.2).trans
      ⟨fun h => ⟨y.2 0, z.2 0, eq_dnfPt y h.1 rfl, eq_dnfPt z h.2.1 rfl, h.2.2⟩, ?_⟩
    rintro ⟨c, x, rfl, rfl, h⟩
    exact ⟨rfl, rfl, h⟩
  · refine (dnfSub_negIn y.1 z.1 y.2 z.2).trans
      ⟨fun h => ⟨y.2 0, z.2 0, eq_dnfPt y h.1 rfl, eq_dnfPt z h.2.1 rfl, h.2.2⟩, ?_⟩
    rintro ⟨c, x, rfl, rfl, h⟩
    exact ⟨rfl, rfl, h⟩

/-- The minuend is a tautology over the images of the variables of the
formula: its models are all the sets of such images. -/
theorem dnfMin_model_iff [Nonempty A] (μ : dnfMinInterp.Map A → Prop) :
    DnfModel (dnfMinInterp.Map A) μ ↔ ∀ y, μ y → ∃ a, y = dnfPt a ∧ SatOccurs A a := by
  have hocc : ∀ y : dnfMinInterp.Map A,
      SatOccurs (dnfMinInterp.Map A) y ↔ ∃ a, y = dnfPt a ∧ SatOccurs A a := by
    intro y
    constructor
    · rintro ⟨c, -, h | h⟩
      · have h' := (dnfMin_posIn c.1 y.1 c.2 y.2).mp h
        exact ⟨y.2 0, eq_dnfPt y h'.2.1 rfl, h'.2.2.1 ▸ h'.2.2.2⟩
      · have h' := (dnfMin_negIn c.1 y.1 c.2 y.2).mp h
        exact ⟨y.2 0, eq_dnfPt y h'.2.1 rfl, h'.2.2.1 ▸ h'.2.2.2⟩
    · rintro ⟨a, rfl, ho⟩
      exact ⟨dnfPt a, (dnfMin_isClause false _).mpr (Or.inr ho),
        Or.inl ((dnfMin_posIn false false _ _).mpr ⟨rfl, rfl, rfl, ho⟩)⟩
  have htaut : ∃ c : dnfMinInterp.Map A, RelMap satIsClause ![c] ∧
      ∀ x, (RelMap satPosIn ![c, x] → μ x) ∧ (RelMap satNegIn ![c, x] → ¬μ x) := by
    by_cases hall : ∀ a : A, SatOccurs A a
    · obtain ⟨a⟩ := ‹Nonempty A›
      by_cases hμ : μ (dnfPt a)
      · refine ⟨dnfPt a, (dnfMin_isClause false _).mpr (Or.inr (hall a)), fun z => ⟨fun hp => ?_,
          fun hn => ?_⟩⟩
        · have h' := (dnfMin_posIn false z.1 _ z.2).mp hp
          rw [eq_dnfPt z h'.2.1 h'.2.2.1]
          exact hμ
        · exact absurd ((dnfMin_negIn false z.1 _ z.2).mp hn).1 (by simp)
      · refine ⟨(true, fun _ => a), (dnfMin_isClause true _).mpr (Or.inl rfl), fun z =>
          ⟨fun hp => ?_, fun hn => ?_⟩⟩
        · exact absurd ((dnfMin_posIn true z.1 _ z.2).mp hp).1 (by simp)
        · have h' := (dnfMin_negIn true z.1 _ z.2).mp hn
          rw [eq_dnfPt z h'.2.1 h'.2.2.1]
          exact hμ
    · obtain ⟨a, ha⟩ := not_forall.mp hall
      refine ⟨(true, fun _ => a), (dnfMin_isClause true _).mpr (Or.inl rfl), fun z =>
        ⟨fun hp => ?_, fun hn => ?_⟩⟩
      · exact absurd ((dnfMin_posIn true z.1 _ z.2).mp hp).1 (by simp)
      · exact absurd ((dnfMin_negIn true z.1 _ z.2).mp hn).2.2.2 ha
  exact ⟨fun h y hy => (hocc y).mp (h.2 y hy), fun h => ⟨htaut, fun y hy => (hocc y).mpr (h y hy)⟩⟩

/-- A witness of the presentation of #DNF at an interpreted instance is a
model of that instance. -/
theorem witAt_sharpDnf (I : FOInterpretation (Language.sat.sum Language.order) Language.sat Bool 1)
    (ρ : satAssignBlock.Assignment (Bool × (Fin 1 → A))) :
    I.WitAt satAssignBlock (orderFreeKernel satAssignBlock sharpDnfKernel) A ρ ↔
      DnfModel (I.Map A) ((satAssignEquiv (I.Map A)).symm ρ) :=
  (I.witAt_orderFreeKernel satAssignBlock A sharpDnfKernel ρ).trans
    (realize_sharpDnfKernel (A := I.Map A) ρ)

end Instances

/-! ### The reduction -/

/-- **#SAT reduces to #DNF by a strong subtractive reduction**
(Proposition 3.4 of [Durand, Hermann, Kolaitis 2005][durand2005subtractive]):
the models of the negated formula are among those of a tautology over the same
variables, and the difference of the two counts is the number of models of the
formula. -/
noncomputable def sharpSat_strongSubtractive_sharpDnf :
    StrongSubtractiveReduction SharpSAT SharpDNF where
  Tag := Bool
  dim := 1
  block := satAssignBlock
  kernel := orderFreeKernel satAssignBlock sharpDnfKernel
  present := fun A _ _ _ _ => (card_dnfModel_eq_witnessCount A).trans
    (witnessCount_orderFreeKernel satAssignBlock sharpDnfKernel A).symm
  subtrahend := dnfSubInterp
  minuend := dnfMinInterp
  witness_le := fun A _ _ _ _ ρ h =>
    (witAt_sharpDnf dnfMinInterp ρ).mpr ((dnfMin_model_iff _).mpr
      ((dnfSub_model_iff _).mp ((witAt_sharpDnf dnfSubInterp ρ).mp h)).1)
  correct := fun A _ _ _ _ => by
    have h1 : SharpDNF (dnfSubInterp.Map A) =
        Nat.card {ν : A → Prop // (∀ a, ν a → SatOccurs A a) ∧ ¬SatModel A ν} :=
      (Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun μ => dnfSub_model_iff μ)).trans
        (card_embedded_sets dnfPt_injective (SatOccurs A) fun ν => ¬SatModel A ν)
    have h2 : SharpDNF (dnfMinInterp.Map A) =
        Nat.card {ν : A → Prop // (∀ a, ν a → SatOccurs A a) ∧ True} :=
      (Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun μ =>
        (dnfMin_model_iff μ).trans (and_iff_left trivial).symm)).trans
        (card_embedded_sets dnfPt_injective (SatOccurs A) fun _ => True)
    have h3 := card_diff_add_card (P := SatModel A)
      (Q := fun ν : A → Prop => ∀ a, ν a → SatOccurs A a) fun ν h => h.2
    have h4 : Nat.card {ν : A → Prop // (∀ a, ν a → SatOccurs A a) ∧ True} =
        Nat.card {ν : A → Prop // ∀ a, ν a → SatOccurs A a} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun ν => and_iff_left trivial)
    rw [h1, h2, h4, ← h3, sharpSat_apply]
    exact Nat.add_comm _ _

/-- #SAT reduces to #DNF by a subtractive reduction. -/
theorem sharpSat_subtractive_sharpDnf : SharpSAT ≤ˢ SharpDNF :=
  sharpSat_strongSubtractive_sharpDnf.subtractiveReducible

/-- **#SAT is `#P`-complete**: parsimoniously, hence under subtractive
reductions. -/
theorem sharpSat_sharpP_complete : SharpP.Complete SharpSAT :=
  ⟨sharpSat_mem_sharpP, hard_sharpP_of_ordered fun D hD =>
    sharpSat_parsimoniousHard_of_sharpPDefinable D hD⟩

/-- **#DNF is `#P`-hard**: every problem of `#P` reduces to #SAT
parsimoniously, and #SAT to #DNF by a strong subtractive reduction. -/
theorem sharpDnf_sharpP_hard : SharpP.Hard SharpDNF :=
  CountingClass.Hard.of_subtractive sharpSat_subtractive_sharpDnf sharpSat_sharpP_complete.hard

/-- **#DNF is `#P`-complete**
(Proposition 3.4 of [Durand, Hermann, Kolaitis 2005][durand2005subtractive]):
it is in `#P`, every problem of `#P` reduces to it by a subtractive reduction,
and `#P` is closed under those. -/
theorem sharpDnf_sharpP_complete : SharpP.Complete SharpDNF :=
  ⟨sharpDnf_mem_sharpP, sharpDnf_sharpP_hard⟩

end DescriptiveComplexity
