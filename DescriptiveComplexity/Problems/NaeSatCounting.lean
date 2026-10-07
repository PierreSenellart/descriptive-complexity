/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.NaeSat
import DescriptiveComplexity.Problems.SetSplitting
import DescriptiveComplexity.Problems.SetFamily.Counting
import DescriptiveComplexity.Problems.Sat.CountingDnf
import DescriptiveComplexity.Numbers.DigitExtract

/-!
# #NAE-SAT and #Set Splitting

The counting versions of `DescriptiveComplexity.NAESAT` and
`DescriptiveComplexity.SetSplitting`. Their solutions come in complementary
pairs, which is why neither is reached parsimoniously; both are one-call
`#P`-complete.

* **#NAE-SAT** (`DescriptiveComplexity.SharpNAESAT`) counts the
  not-all-equal models among the sets of *variables of the formula*, the
  convention of #SAT, so that flipping a model inside the variables is again
  a model. The reduction from #SAT is that of the decision problem unchanged,
  one fresh variable added positively to every clause: a model of the result
  is a model of the formula with the fresh variable false, or its flip
  (`DescriptiveComplexity.NaeCount.card_naeModel_map`), so the count is halved,
  rounding up for the formula with no clause, whose only model is empty.
* **#Set Splitting** (`DescriptiveComplexity.SharpSetSplitting`) counts the
  color classes of ground elements splitting every set. The reduction from
  #NAE-SAT is again that of the decision problem: a splitting of the literal
  set system is an assignment of *every* element, the variables of the formula
  and the others alike, and each element that is no variable doubles the
  count (`DescriptiveComplexity.NaeCount.card_split_map`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc

/-! ### #NAE-SAT -/

section Problem

variable (A : Type) [Language.sat.Structure A]

/-- A **not-all-equal model**: a not-all-equal proper set of variables of the
formula. -/
def NAEModel (ν : A → Prop) : Prop :=
  NAEProper ν ∧ ∀ x : A, ν x → SatOccurs A x

/-- The first-order kernel of #NAE-SAT. -/
noncomputable def sharpNaeKernel : satSOLang.Sentence :=
  naeKernel ⊓ satVarKernel

variable {A}

theorem realize_sharpNaeKernel (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) sharpNaeKernel) ↔
      NAEModel A ((satAssignEquiv A).symm ρ) := by
  have h1 := realize_naeKernel ρ
  have h2 := realize_satVarKernel ρ
  let := satAssignBlock.structure ρ
  rw [sharpNaeKernel, Sentence.Realize, Formula.realize_inf]
  refine and_congr (h1.trans ?_) h2
  exact ⟨fun ⟨h, h'⟩ c hc => ⟨h c hc, h' c hc⟩, fun h => ⟨fun c hc => (h c hc).1,
    fun c hc => (h c hc).2⟩⟩

variable (A) in
theorem card_naeModel_eq_witnessCount :
    Nat.card {ν : A → Prop // NAEModel A ν} = witnessCount satAssignBlock sharpNaeKernel A :=
  Nat.card_congr (Equiv.subtypeEquiv (satAssignEquiv A) fun ν => by
    rw [realize_sharpNaeKernel, Equiv.symm_apply_apply])

end Problem

/-- **#NAE-SAT**: the number of not-all-equal models of a CNF formula. -/
noncomputable def SharpNAESAT : CountingProblem Language.sat where
  Count := fun A inst => Nat.card {ν : A → Prop // @NAEModel A inst ν}
  iso_invariant := fun {A B} _ _ e => by
    rw [card_naeModel_eq_witnessCount A, card_naeModel_eq_witnessCount B]
    exact witnessCount_iso satAssignBlock sharpNaeKernel e

theorem sharpNaeSat_apply (A : Type) [Language.sat.Structure A] :
    SharpNAESAT A = Nat.card {ν : A → Prop // NAEModel A ν} :=
  rfl

/-- **#NAE-SAT is in `#P`.** -/
theorem sharpNaeSat_mem_sharpP : SharpNAESAT ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => (card_naeModel_eq_witnessCount A).symm)
    (sharpPDefinable_ofKernel satAssignBlock sharpNaeKernel)

namespace NaeCount

section Generic

variable {A : Type} [Language.sat.Structure A]

/-- Not-all-equal properness only reads the variables of the formula. -/
theorem naeProper_congr {ν ν' : A → Prop} (h : ∀ x, SatOccurs A x → (ν x ↔ ν' x))
    (hν : NAEProper ν) : NAEProper ν' := by
  intro c hc
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hν c hc
  have hxo : SatOccurs A x := ⟨c, hc, hx.elim (fun h => Or.inl h.1) fun h => Or.inr h.1⟩
  have hyo : SatOccurs A y := ⟨c, hc, hy.elim (fun h => Or.inl h.1) fun h => Or.inr h.1⟩
  refine ⟨⟨x, ?_⟩, ⟨y, ?_⟩⟩
  · rw [← h x hxo]
    exact hx
  · rw [← h y hyo]
    exact hy

/-- The flip of a model inside the variables of the formula. -/
def flip (ν : A → Prop) (x : A) : Prop :=
  SatOccurs A x ∧ ¬ν x

theorem naeModel_flip {ν : A → Prop} (h : NAEModel A ν) : NAEModel A (flip ν) :=
  ⟨naeProper_congr (fun _ hx => (and_iff_right hx).symm) h.1.not, fun _ hx => hx.1⟩

theorem flip_flip {ν : A → Prop} (h : NAEModel A ν) : flip (flip ν) = ν :=
  funext fun x => propext ⟨fun hx => not_not.mp fun h' => hx.2 ⟨hx.1, h'⟩,
    fun hx => ⟨h.2 x hx, fun h' => h'.2 hx⟩⟩

open Classical in
/-- **The models come in pairs**: a variable `q` of the formula is false in
exactly half of them. -/
theorem card_naeModel_eq_two_mul [Finite A] {q : A} (hq : SatOccurs A q) :
    Nat.card {ν : A → Prop // NAEModel A ν} =
      2 * Nat.card {ν : A → Prop // NAEModel A ν ∧ ¬ν q} := by
  have e1 : {ν : A → Prop // NAEModel A ν} ≃
      {ν : A → Prop // NAEModel A ν ∧ ¬ν q} ⊕ {ν : A → Prop // NAEModel A ν ∧ ν q} :=
    { toFun := fun ν => if h : ν.1 q then Sum.inr ⟨ν.1, ν.2, h⟩ else Sum.inl ⟨ν.1, ν.2, h⟩
      invFun := Sum.elim (fun ν => ⟨ν.1, ν.2.1⟩) fun ν => ⟨ν.1, ν.2.1⟩
      left_inv := fun ν => by by_cases h : ν.1 q <;> simp [h]
      right_inv := by
        rintro (ν | ν)
        · simp [ν.2.2]
        · simp [ν.2.2] }
  have e2 : {ν : A → Prop // NAEModel A ν ∧ ¬ν q} ≃ {ν : A → Prop // NAEModel A ν ∧ ν q} :=
    { toFun := fun ν => ⟨flip ν.1, naeModel_flip ν.2.1, hq, ν.2.2⟩
      invFun := fun ν => ⟨flip ν.1, naeModel_flip ν.2.1, fun h => h.2 ν.2.2⟩
      left_inv := fun ν => Subtype.ext (flip_flip ν.2.1)
      right_inv := fun ν => Subtype.ext (flip_flip ν.2.1) }
  rw [Nat.card_congr e1, Nat.card_sum, ← Nat.card_congr e2, two_mul]

open Classical in
/-- **The not-all-equal assignments of every element**: each element that is
no variable of the formula doubles the count of the models. -/
theorem card_naeProper [Finite A] :
    Nat.card {ν : A → Prop // NAEProper ν} =
      Nat.card {ν : A → Prop // NAEModel A ν} * 2 ^ Nat.card {x : A // ¬SatOccurs A x} := by
  rw [← card_subsets_eq_two_pow, ← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun ν => (⟨fun x => ν.1 x ∧ SatOccurs A x,
          naeProper_congr (fun x hx => by simp [hx]) ν.2, fun _ h => h.2⟩,
        ⟨fun x => ν.1 x ∧ ¬SatOccurs A x, fun _ h => h.2⟩)
      invFun := fun p => ⟨fun x => p.1.1 x ∨ p.2.1 x, naeProper_congr (fun x hx => by
          have := p.2.2 x
          constructor
          · intro h
            exact Or.inl h
          · rintro (h | h)
            · exact h
            · exact absurd hx (this h)) p.1.2.1⟩
      left_inv := fun ν => Subtype.ext (funext fun x => propext (by
        by_cases h : SatOccurs A x <;> simp [h]))
      right_inv := fun p => Prod.ext (Subtype.ext (funext fun x => propext ?_))
        (Subtype.ext (funext fun x => propext ?_)) }
  · have h := p.1.2.2 x
    have h' := p.2.2 x
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact h1
      · exact absurd h2 (h' h1)
    · intro h1
      exact ⟨Or.inl h1, h h1⟩
  · have h := p.1.2.2 x
    have h' := p.2.2 x
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (h h1) h2
      · exact h1
    · intro h1
      exact ⟨Or.inr h1, h' h1⟩

/-- A formula with no clause has the empty model only. -/
theorem card_naeModel_of_no_clause [Finite A] (h : ∀ c : A, ¬RelMap satIsClause ![c]) :
    Nat.card {ν : A → Prop // NAEModel A ν} = 1 := by
  refine Nat.card_eq_one_iff_exists.mpr ⟨⟨fun _ => False, fun c hc => absurd hc (h c),
    fun _ h => h.elim⟩, fun ν => Subtype.ext (funext fun x => propext ⟨fun hx => ?_, False.elim⟩)⟩
  obtain ⟨c, hc, -⟩ := ν.2.2 x hx
  exact h c hc

/-- A formula with no clause has the empty model only, for #SAT too. -/
theorem card_satModel_of_no_clause [Finite A] (h : ∀ c : A, ¬RelMap satIsClause ![c]) :
    Nat.card {ν : A → Prop // SatModel A ν} = 1 := by
  refine Nat.card_eq_one_iff_exists.mpr ⟨⟨fun _ => False, fun c hc => absurd hc (h c),
    fun _ h => h.elim⟩, fun ν => Subtype.ext (funext fun x => propext ⟨fun hx => ?_, False.elim⟩)⟩
  obtain ⟨c, hc, -⟩ := ν.2.2 x hx
  exact h c hc

end Generic

/-! ### The fresh variable -/

section Fresh

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
theorem oPt_injective : Function.Injective (oPt (A := A)) := fun _ _ h =>
  congrFun (congrArg Prod.snd h) 0

omit [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A] in
theorem oPt_ne_xPt (x y : A) : oPt x ≠ xPt y := fun h =>
  Bool.noConfusion (congrArg Prod.fst h)

/-- The least element. -/
noncomputable def least (A : Type) [LinearOrder A] [Finite A] [Nonempty A] : A :=
  Classical.choose (Finite.exists_min (id : A → A))

omit [Language.sat.Structure A] in
theorem least_le (a : A) : least A ≤ a :=
  Classical.choose_spec (Finite.exists_min (id : A → A)) a

/-- The variables of the formula with the fresh variable: those of the formula,
and the fresh variable when there is a clause. -/
theorem satOccurs_map (p : naeInterp.Map A) :
    SatOccurs (naeInterp.Map A) p ↔ (∃ x, p = oPt x ∧ SatOccurs A x) ∨
      (p = xPt (least A) ∧ ∃ c : A, RelMap satIsClause ![c]) := by
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨c', rfl⟩ : ∃ c', c = oPt c' := by
      rcases eq_oPt_or_xPt c with ⟨c', rfl⟩ | ⟨v, rfl⟩
      · exact ⟨c', rfl⟩
      · exact absurd hc (nae_isClause_x v)
    have hc' := (nae_isClause_o c').mp hc
    rcases eq_oPt_or_xPt p with ⟨x, rfl⟩ | ⟨v, rfl⟩
    · refine Or.inl ⟨x, rfl, c', hc', ?_⟩
      rcases h with h | h
      · exact Or.inl ((nae_pos_oo c' x).mp h)
      · exact Or.inr ((nae_neg_oo c' x).mp h)
    · rcases h with h | h
      · obtain ⟨-, hmin⟩ := (nae_pos_ox c' v).mp h
        exact Or.inr ⟨by rw [le_antisymm (hmin _) (least_le v)], c', hc'⟩
      · exact absurd h (nae_neg_ox c' v)
  · rintro (⟨x, rfl, c, hc, h⟩ | ⟨rfl, c, hc⟩)
    · refine ⟨oPt c, (nae_isClause_o c).mpr hc, ?_⟩
      rcases h with h | h
      · exact Or.inl ((nae_pos_oo c x).mpr h)
      · exact Or.inr ((nae_neg_oo c x).mpr h)
    · exact ⟨oPt c, (nae_isClause_o c).mpr hc,
        Or.inl ((nae_pos_ox c _).mpr ⟨hc, least_le⟩)⟩

/-- **The models with the fresh variable false are the models of the
formula.** -/
noncomputable def freshFalseEquiv :
    {μ : naeInterp.Map A → Prop // NAEModel _ μ ∧ ¬μ (xPt (least A))} ≃
      {ν : A → Prop // SatModel A ν} where
  toFun μ := ⟨fun x => μ.1 (oPt x), fun c hc => by
      obtain ⟨p, hp⟩ := (μ.2.1.1 (oPt c) ((nae_isClause_o c).mpr hc)).1
      rcases eq_oPt_or_xPt p with ⟨x, rfl⟩ | ⟨v, rfl⟩
      · rcases hp with ⟨h, hT⟩ | ⟨h, hT⟩
        · exact ⟨x, Or.inl ⟨(nae_pos_oo c x).mp h, hT⟩⟩
        · exact ⟨x, Or.inr ⟨(nae_neg_oo c x).mp h, hT⟩⟩
      · rcases hp with ⟨h, hT⟩ | ⟨h, -⟩
        · obtain ⟨-, hmin⟩ := (nae_pos_ox c v).mp h
          rw [le_antisymm (hmin _) (least_le v)] at hT
          exact absurd hT μ.2.2
        · exact absurd h (nae_neg_ox c v),
    fun x hx => by
      rcases (satOccurs_map _).mp (μ.2.1.2 _ hx) with ⟨y, hy, hyo⟩ | ⟨h, -⟩
      · exact oPt_injective hy ▸ hyo
      · exact absurd h (oPt_ne_xPt _ _)⟩
  invFun ν := ⟨fun p => ∃ x, p = oPt x ∧ ν.1 x, ⟨fun p hp => by
      obtain ⟨c, rfl⟩ : ∃ c, p = oPt c := by
        rcases eq_oPt_or_xPt p with ⟨c, rfl⟩ | ⟨v, rfl⟩
        · exact ⟨c, rfl⟩
        · exact absurd hp (nae_isClause_x v)
      have hc := (nae_isClause_o c).mp hp
      refine ⟨?_, ⟨xPt (least A), Or.inl ⟨(nae_pos_ox c _).mpr ⟨hc, least_le⟩,
        fun ⟨x, hx, _⟩ => oPt_ne_xPt x _ hx.symm⟩⟩⟩
      obtain ⟨x, hx⟩ := ν.2.1 c hc
      rcases hx with ⟨h, hT⟩ | ⟨h, hT⟩
      · exact ⟨oPt x, Or.inl ⟨(nae_pos_oo c x).mpr h, x, rfl, hT⟩⟩
      · exact ⟨oPt x, Or.inr ⟨(nae_neg_oo c x).mpr h, fun ⟨y, hy, hy'⟩ =>
          hT (oPt_injective hy ▸ hy')⟩⟩,
    fun p ⟨x, hp, hx⟩ => (satOccurs_map p).mpr (Or.inl ⟨x, hp, ν.2.2 x hx⟩)⟩,
    fun ⟨x, hx, _⟩ => oPt_ne_xPt x _ hx.symm⟩
  left_inv μ := Subtype.ext (funext fun p => propext (by
    constructor
    · rintro ⟨x, rfl, hx⟩
      exact hx
    · intro hp
      rcases (satOccurs_map p).mp (μ.2.1.2 p hp) with ⟨y, rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨y, rfl, hp⟩
      · exact absurd hp μ.2.2))
  right_inv ν := Subtype.ext (funext fun x => propext ⟨fun ⟨y, hy, hy'⟩ =>
    oPt_injective hy ▸ hy', fun h => ⟨x, rfl, h⟩⟩)

/-- **The count of the formula with the fresh variable**: twice the count of
the formula when there is a clause. -/
theorem card_naeModel_map :
    SharpNAESAT (naeInterp.Map A) + 1 = 2 * SharpSAT A + 1 ∨
      (SharpNAESAT (naeInterp.Map A) = 1 ∧ SharpSAT A = 1) := by
  have : Finite (naeInterp.Map A) := naeInterp.map_finite A
  rw [sharpNaeSat_apply, sharpSat_apply]
  by_cases hc : ∃ c : A, RelMap satIsClause ![c]
  · left
    rw [card_naeModel_eq_two_mul ((satOccurs_map _).mpr (Or.inr ⟨rfl, hc⟩)),
      Nat.card_congr freshFalseEquiv]
  · right
    push Not at hc
    refine ⟨card_naeModel_of_no_clause fun p hp => ?_, card_satModel_of_no_clause hc⟩
    rcases eq_oPt_or_xPt p with ⟨c, rfl⟩ | ⟨v, rfl⟩
    · exact hc c ((nae_isClause_o c).mp hp)
    · exact nae_isClause_x v hp

end Fresh

end NaeCount

open NaeCount in
/-- **#SAT reduces to #NAE-SAT with one call**: add one fresh variable to every
clause, and halve the count, rounding up. -/
noncomputable def sharpSat_oneCall_sharpNaeSat : SharpSAT ≤ᶜ[≤] SharpNAESAT where
  Tag := Bool
  dim := 1
  toRelInterpretation := naeInterp.toRel
  dom_nonempty := fun A _ _ _ _ =>
    ⟨true, fun _ => Classical.arbitrary A, Formula.realize_top.mpr trivial⟩
  post := .div (.add .oracle (.poly (.num 1))) (.poly (.num 2))
  correct := fun A _ _ _ _ => by
    change SharpSAT A = (SharpNAESAT (naeInterp.toRel.MapRel A) + 1) / 2
    rw [← SharpNAESAT.iso_invariant (naeInterp.toRelLEquiv A)]
    rcases card_naeModel_map (A := A) with h | ⟨h1, h2⟩
    · omega
    · rw [h1, h2]

/-- **#NAE-SAT is one-call `#P`-complete.**
Registered in the Lax archive as
[`Lax859101.NaeSatComplete.sharpNaeSat_sharpP_oneCallComplete`](https://laxarchive.org/lax-859101/Lax859101.NaeSatComplete.html#s-Lax859101.NaeSatComplete.sharpNaeSat_sharpP_oneCallComplete). -/
theorem sharpNaeSat_sharpP_oneCallComplete : SharpP.OneCallComplete SharpNAESAT :=
  .of_mem sharpNaeSat_mem_sharpP (CountingClass.OneCallHard.of_oneCall
    sharpSat_oneCall_sharpNaeSat
    (oneCallHard_sharpP_of_parsimoniousHard sharpSat_sharpP_parsimoniousHard))

/-! ### #Set Splitting -/

section Split

variable (A : Type) [Language.setSystem.Structure A]

/-- A **splitting color class**: a set of ground elements meeting every set of
the family and its complement. -/
def SplitColoring (S : A → Prop) : Prop :=
  (∀ x : A, S x → SSElem x) ∧ ∀ f : A, SSFam f →
    (∃ x : A, SSElem x ∧ SSMem x f ∧ S x) ∧ ∃ x : A, SSElem x ∧ SSMem x f ∧ ¬S x

/-- **The splitting color classes are the witnesses of the counting
kernel**, bijectively. -/
def splitColoringEquiv :
    {ρ : familyGuessBlock.Assignment A //
        @Sentence.Realize setFamilySOLang A
          (@sumStructure _ _ A _ (familyGuessBlock.structure ρ)) sharpSetSplittingKernel} ≃
      {S : A → Prop // SplitColoring A S} where
  toFun ρ := ⟨fun s => ρ.1 .guess ![s], by
    obtain ⟨⟨h1, h2⟩, h3, -⟩ := (realize_sharpSetSplittingKernel ρ.1).mp ρ.2
    exact ⟨h3, fun f hf => ⟨h1 f hf, h2 f hf⟩⟩⟩
  invFun S := ⟨familyGuessOf S.1, (realize_sharpSetSplittingKernel _).mpr
    ⟨⟨fun f hf => (S.2.2 f hf).1, fun f hf => (S.2.2 f hf).2⟩, S.2.1, fun _ _ h => h⟩⟩
  left_inv := by
    rintro ⟨ρ, hρ⟩
    have hinj := ((realize_sharpSetSplittingKernel ρ).mp hρ).2.2
    refine Subtype.ext (funext fun i => ?_)
    cases i with
    | guess =>
      refine funext fun (w : Fin 1 → A) => ?_
      exact congrArg (ρ .guess) (funext fun k => by fin_cases k; rfl)
    | inj =>
      refine funext fun (w : Fin 2 → A) => propext ⟨fun h => h.elim, fun h => ?_⟩
      refine hinj (w 0) (w 1) ?_
      exact (congrArg (ρ .inj) (funext fun k => by fin_cases k <;> rfl)).mpr h
  right_inv := fun _ => rfl

end Split

/-- **#Set Splitting**: the number of color classes of ground elements
splitting every set of the family. -/
noncomputable def SharpSetSplitting : CountingProblem Language.setSystem where
  Count := fun A inst => Nat.card {S : A → Prop // @SplitColoring A inst S}
  iso_invariant := fun {A B} _ _ e => by
    rw [← Nat.card_congr (splitColoringEquiv A), ← Nat.card_congr (splitColoringEquiv B)]
    exact witnessCount_iso familyGuessBlock sharpSetSplittingKernel e

theorem sharpSetSplitting_apply (A : Type) [Language.setSystem.Structure A] :
    SharpSetSplitting A = Nat.card {S : A → Prop // SplitColoring A S} :=
  rfl

/-- **#Set Splitting is in `#P`.** -/
theorem sharpSetSplitting_mem_sharpP : SharpSetSplitting ∈ SharpP :=
  sharpPDefinable_congr (fun A _ _ => Nat.card_congr (splitColoringEquiv A))
    (sharpPDefinable_ofKernel familyGuessBlock sharpSetSplittingKernel)

namespace NaeCount

open SetSplitRed

section SplitMap

variable {A : Type} [Language.sat.Structure A]

/-- A splitting of the literal set system gives the two literals of every
element opposite colors. -/
theorem split_lit_false {S : splInterp.Map A → Prop} (hS : SplitColoring _ S) (y : A) :
    S (splPt (.lit false) y) ↔ ¬S (splPt (.lit true) y) := by
  obtain ⟨⟨p, hpe, hpm, hp⟩, ⟨q, hqe, hqm, hq⟩⟩ := hS.2 (splPt .pairSet y) (ssFam_pairSet y)
  obtain ⟨s, x, rfl⟩ := ssElem_cases hpe
  obtain ⟨t, z, rfl⟩ := ssElem_cases hqe
  obtain rfl := (ssMem_lit_pairSet s x y).mp hpm
  obtain rfl := (ssMem_lit_pairSet t z x).mp hqm
  cases s <;> cases t
  · exact absurd hp hq
  · exact ⟨fun _ => hq, fun _ => hp⟩
  · exact ⟨fun h h' => hq h, fun h => absurd hp h⟩
  · exact absurd hp hq

/-- The color of a literal is its truth value under the assignment read off
the positive literals. -/
theorem split_litTrue {S : splInterp.Map A → Prop} (hS : SplitColoring _ S) (s : Bool) (y : A) :
    S (splPt (.lit s) y) ↔ LitTrue (fun x => S (splPt (.lit true) x)) y s := by
  cases s
  · exact split_lit_false hS y
  · exact Iff.rfl

/-- **The splittings of the literal set system are the not-all-equal
assignments of every element.** -/
noncomputable def splitEquiv :
    {S : splInterp.Map A → Prop // SplitColoring _ S} ≃ {ν : A → Prop // NAEProper ν} where
  toFun S := ⟨fun x => S.1 (splPt (.lit true) x), naeProper_of_occ fun c hc => by
      obtain ⟨⟨p, hpe, hpm, hp⟩, ⟨q, hqe, hqm, hq⟩⟩ :=
        S.2.2 (splPt .clSet c) ((ssFam_clSet c).mpr hc)
      obtain ⟨s, x, rfl⟩ := ssElem_cases hpe
      obtain ⟨t, z, rfl⟩ := ssElem_cases hqe
      exact ⟨⟨x, s, (ssMem_lit_clSet s x c).mp hpm, (split_litTrue S.2 s x).mp hp⟩,
        ⟨z, t, (ssMem_lit_clSet t z c).mp hqm, fun h => hq ((split_litTrue S.2 t z).mpr h)⟩⟩⟩
  invFun ν := ⟨fun p => ∃ s x, p = splPt (.lit s) x ∧ LitTrue ν.1 x s,
    ⟨fun p ⟨s, x, hp, _⟩ => hp ▸ ssElem_lit s x, fun f hf => by
      have hcol : ∀ (s : Bool) (x : A),
          (∃ s' x', splPt (.lit s) x = splPt (.lit s') x' ∧ LitTrue ν.1 x' s') ↔
            LitTrue ν.1 x s := fun s x =>
        ⟨fun ⟨s', x', h, hT⟩ => by
          obtain ⟨hs, rfl⟩ := splPt_eq_iff.mp h
          cases hs
          exact hT, fun h => ⟨s, x, rfl, h⟩⟩
      rcases ssFam_cases hf with ⟨y, rfl⟩ | ⟨c, hc, rfl⟩
      · by_cases hy : ν.1 y
        · exact ⟨⟨_, ssElem_lit true y, (ssMem_lit_pairSet true y y).mpr rfl, (hcol true y).mpr hy⟩,
            ⟨_, ssElem_lit false y, (ssMem_lit_pairSet false y y).mpr rfl,
              fun h => (hcol false y).mp h hy⟩⟩
        · exact ⟨⟨_, ssElem_lit false y, (ssMem_lit_pairSet false y y).mpr rfl,
              (hcol false y).mpr hy⟩,
            ⟨_, ssElem_lit true y, (ssMem_lit_pairSet true y y).mpr rfl,
              fun h => hy ((hcol true y).mp h)⟩⟩
      · obtain ⟨⟨x, s, hx, hT⟩, ⟨z, t, hz, hF⟩⟩ := naeProper_occ ν.2 c hc
        exact ⟨⟨_, ssElem_lit s x, (ssMem_lit_clSet s x c).mpr hx, (hcol s x).mpr hT⟩,
          ⟨_, ssElem_lit t z, (ssMem_lit_clSet t z c).mpr hz, fun h => hF ((hcol t z).mp h)⟩⟩⟩⟩
  left_inv S := Subtype.ext (funext fun p => propext (by
    constructor
    · rintro ⟨s, x, rfl, hT⟩
      exact (split_litTrue S.2 s x).mpr hT
    · intro hp
      obtain ⟨s, x, rfl⟩ := ssElem_cases (S.2.1 p hp)
      exact ⟨s, x, rfl, (split_litTrue S.2 s x).mp hp⟩))
  right_inv ν := Subtype.ext (funext fun x => propext ⟨fun ⟨s, y, h, hT⟩ => by
      obtain ⟨hs, rfl⟩ := splPt_eq_iff.mp h
      cases hs
      exact hT, fun h => ⟨true, x, rfl, h⟩⟩)

/-- **The count of the literal set system**: the count of the formula, doubled
for each element that is no variable of it. -/
theorem card_split_map [Finite A] :
    SharpSetSplitting (splInterp.Map A) =
      SharpNAESAT A * 2 ^ Nat.card {x : A // ¬SatOccurs A x} := by
  rw [sharpSetSplitting_apply, sharpNaeSat_apply, Nat.card_congr splitEquiv, card_naeProper]

end SplitMap

end NaeCount

/-- The number of elements that are no variable of the formula, as a
polynomial term. -/
noncomputable def nonVarCount : PolyTerm Language.sat :=
  .count (∼satOccursFormula)

theorem eval_nonVarCount (A : Type) [Language.sat.Structure A] [LinearOrder A] :
    nonVarCount.eval A = Nat.card {x : A // ¬SatOccurs A x} := by
  rw [nonVarCount, PolyTerm.eval_count_one]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by
    rw [Formula.realize_not, realize_satOccursFormula])

open NaeCount SetSplitRed in
/-- **#NAE-SAT reduces to #Set Splitting with one call**: the literal set
system, its count divided by `2` to the number of elements that are no
variable of the formula. -/
noncomputable def sharpNaeSat_oneCall_sharpSetSplitting : SharpNAESAT ≤ᶜ[≤] SharpSetSplitting :=
  (SharpSetSplitting.pullbackReduction splInterp).toOneCall.ofPost
    (.div .oracle (.pow2 nonVarCount)) fun A _ _ _ _ => by
      change SharpNAESAT A = SharpSetSplitting (splInterp.Map A) / 2 ^ nonVarCount.eval A
      rw [eval_nonVarCount, card_split_map, Nat.mul_div_cancel _ (by positivity)]

/-- **#Set Splitting is one-call `#P`-complete.**
Registered in the Lax archive as
[`Lax859101.NaeSatComplete.sharpSetSplitting_sharpP_oneCallComplete`](https://laxarchive.org/lax-859101/Lax859101.NaeSatComplete.html#s-Lax859101.NaeSatComplete.sharpSetSplitting_sharpP_oneCallComplete). -/
theorem sharpSetSplitting_sharpP_oneCallComplete : SharpP.OneCallComplete SharpSetSplitting :=
  .of_mem sharpSetSplitting_mem_sharpP (CountingClass.OneCallHard.of_oneCall
    sharpNaeSat_oneCall_sharpSetSplitting sharpNaeSat_sharpP_oneCallComplete.oneCallHard)

end DescriptiveComplexity
