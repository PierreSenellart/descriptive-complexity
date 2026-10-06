/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CycleCover.Base

/-!
# The consistent choices are the exactly-one models

A consistent choice of loops (`DescriptiveComplexity.SatCover.Consistent`)
reads as an assignment: a variable is true when the track loop of its
positive dummy occurrence is chosen (`DescriptiveComplexity.SatCover.toModel`).
Since the track of a literal is used entirely or not at all, the track loops
chosen are exactly those of the true literals, and the one free spoke of each
clause is its one true literal: the assignment is an exactly-one model, and
the correspondence is a bijection
(`DescriptiveComplexity.SatCover.consistentEquiv`). Hence the permanent of
the base graph with the gadgets attached is `4` to the number of occurrences
times the number of exactly-one models
(`DescriptiveComplexity.SatCover.bperm_attachAll_sites_eq`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc Finset

namespace SatCover

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Fintype A]

/-! ### The tracks of a consistent choice -/

/-- **The track of a literal is chosen entirely or not at all.** -/
theorem chain_all_or_none {U : Finset (Occ A)} (hU : Consistent U) (x : A) (s : Bool) :
    (∀ o : Occ A, o.x = x → o.s = s → o ∈ U) ∨ ∀ o : Occ A, o.x = x → o.s = s → o ∉ U := by
  classical
  by_cases hx : SatOccurs A x
  · let T : Finset (WithBot A) := (U.filter fun o : Occ A => o.x = x ∧ o.s = s).image Occ.c
    have hmemT : ∀ c, c ∈ T ↔ ∃ o ∈ U, o.x = x ∧ o.s = s ∧ o.c = c := fun c => by
      simp only [T, mem_image, mem_filter]
      exact exists_congr fun o => ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩,
        fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩⟩
    have hvalid : ∀ c ∈ chain x s, OccValid (c, x, s) := fun c hc => by
      rcases mem_chain.mp hc with rfl | ⟨c', rfl, h⟩
      · exact Or.inl ⟨rfl, hx⟩
      · exact Or.inr ⟨c', rfl, h⟩
    have hTS : T ⊆ chain x s := fun c hc => by
      obtain ⟨o, -, hox, hos, rfl⟩ := (hmemT c).mp hc
      exact hox ▸ hos ▸ c_mem_chain o
    have hcl : ∀ c ∈ T, cycNext (chain x s) c ∈ T := fun c hc => by
      obtain ⟨o, ho, hox, hos, rfl⟩ := (hmemT c).mp hc
      refine (hmemT _).mpr ⟨nextOcc o, hU.1 o ho, hox, hos, ?_⟩
      rw [nextOcc_c, hox, hos]
    have hcl' : ∀ c ∈ chain x s, c ∉ T → cycNext (chain x s) c ∉ T := fun c hc hcT hnext => by
      obtain ⟨o', ho', hox', hos', hc'⟩ := (hmemT _).mp hnext
      have ho : (⟨(c, x, s), hvalid c hc⟩ : Occ A) ∉ U := fun h =>
        hcT ((hmemT c).mpr ⟨_, h, rfl, rfl, rfl⟩)
      have : nextOcc ⟨(c, x, s), hvalid c hc⟩ = o' := Occ.ext hc'.symm hox'.symm hos'.symm
      exact hU.2.1 _ ho (this ▸ ho')
    rcases eq_empty_or_eq_of_cycNext_closed hTS hcl hcl' with hT | hT
    · refine Or.inr fun o hox hos ho => ?_
      have : o.c ∈ T := (hmemT _).mpr ⟨o, ho, hox, hos, rfl⟩
      rw [hT] at this
      exact notMem_empty _ this
    · refine Or.inl fun o hox hos => ?_
      have : o.c ∈ T := hT ▸ (hox ▸ hos ▸ c_mem_chain o)
      obtain ⟨o', ho', hox', hos', hc'⟩ := (hmemT _).mp this
      exact Occ.ext hc'.symm (hox.trans hox'.symm) (hos.trans hos'.symm) ▸ ho'
  · exact Or.inr fun o hox _ _ => hx (hox ▸ o.satOccurs)

/-- An occurrence is chosen iff the dummy occurrence of its literal is. -/
theorem mem_iff_dummy_mem {U : Finset (Occ A)} (hU : Consistent U) (o : Occ A) :
    o ∈ U ↔ Occ.dummy o.x o.satOccurs o.s ∈ U := by
  rcases chain_all_or_none hU o.x o.s with h | h
  · exact ⟨fun _ => h _ rfl rfl, fun _ => h o rfl rfl⟩
  · exact ⟨fun ho => absurd ho (h o rfl rfl), fun ho => absurd ho (h _ rfl rfl)⟩

/-- Exactly one of the two dummy occurrences of a variable is chosen. -/
theorem dummy_true_mem_iff {U : Finset (Occ A)} (hU : Consistent U) (x : A)
    (hx : SatOccurs A x) : Occ.dummy x hx true ∈ U ↔ Occ.dummy x hx false ∉ U := by
  obtain ⟨o, ⟨hoh, ho⟩, huniq⟩ := hU.2.2 (Sum.inr ⟨x, hx⟩)
  obtain ⟨hob, hox⟩ := (hubOf_eq_inr_iff o ⟨x, hx⟩).mp hoh
  have ho' : o = Occ.dummy x hx o.s := Occ.ext hob hox rfl
  have hd : ∀ s, hubOf (Occ.dummy x hx s) = Sum.inr ⟨x, hx⟩ := fun s =>
    (hubOf_eq_inr_iff _ _).mpr ⟨rfl, rfl⟩
  constructor
  · intro ht hf
    have h1 := huniq _ ⟨hd true, ht⟩
    have h2 := huniq _ ⟨hd false, hf⟩
    exact Bool.false_ne_true (congrArg Occ.s (h2.trans h1.symm))
  · intro hf
    cases hs : o.s
    · rw [hs] at ho'
      exact absurd (ho' ▸ ho) hf
    · rw [hs] at ho'
      exact ho' ▸ ho

/-! ### From choices to models -/

/-- **The assignment read off a choice**: a variable is true when the track
loop of its positive dummy occurrence is chosen. -/
def toModel (U : Finset (Occ A)) (x : A) : Prop :=
  ∃ hx : SatOccurs A x, Occ.dummy x hx true ∈ U

/-- A literal is true under the assignment read off a consistent choice iff
its occurrences are chosen. -/
theorem litTrue_toModel_iff {U : Finset (Occ A)} (hU : Consistent U) (o : Occ A) :
    LitTrue (toModel U) o.x o.s ↔ o ∈ U := by
  rw [mem_iff_dummy_mem hU o]
  cases hs : o.s
  · simp only [LitTrue, Bool.false_eq_true, ↓reduceIte, toModel, not_exists]
    exact ⟨fun h => not_not.mp ((dummy_true_mem_iff hU o.x o.satOccurs).not.mp (h o.satOccurs)),
      fun hf _ ht => (dummy_true_mem_iff hU _ _).mp ht hf⟩
  · simp only [LitTrue, ↓reduceIte, toModel]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨_, h⟩⟩

/-- **The assignment read off a consistent choice is an exactly-one model.** -/
theorem oneInModel_toModel {U : Finset (Occ A)} (hU : Consistent U) : OneInModel A (toModel U) := by
  refine ⟨fun c hc => ?_, fun x ⟨hx, _⟩ => hx⟩
  obtain ⟨o, ⟨hoh, ho⟩, huniq⟩ := hU.2.2 (Sum.inl ⟨c, hc⟩)
  have hoc : o.c = c := (hubOf_eq_inl_iff o ⟨c, hc⟩).mp hoh
  refine ⟨o.x, o.s, o.occIn_of_coe hoc, (litTrue_toModel_iff hU o).mpr ho, fun y t hyt hlit => ?_⟩
  have h := huniq (Occ.real c y t hyt) ⟨(hubOf_eq_inl_iff _ _).mpr rfl,
    (litTrue_toModel_iff hU (Occ.real c y t hyt)).mp hlit⟩
  exact ⟨congrArg Occ.x h, congrArg Occ.s h⟩

/-! ### From models to choices -/

open Classical in
/-- **The choice read off an assignment**: the occurrences of the true
literals. -/
noncomputable def ofModel (ν : A → Prop) : Finset (Occ A) :=
  univ.filter fun o : Occ A => LitTrue ν o.x o.s

omit [LinearOrder A] in
theorem mem_ofModel {ν : A → Prop} {o : Occ A} : o ∈ ofModel ν ↔ LitTrue ν o.x o.s := by
  classical
  simp [ofModel]

open Classical in
/-- **The choice read off an exactly-one model is consistent.** -/
theorem consistent_ofModel {ν : A → Prop} (hν : OneInModel A ν) : Consistent (ofModel ν) := by
  refine ⟨fun o ho => ?_, fun o ho => ?_, fun h => ?_⟩
  · rw [mem_ofModel] at ho ⊢
    exact ho
  · rw [mem_ofModel] at ho ⊢
    exact ho
  rcases h with ⟨c, hc⟩ | ⟨x, hx⟩
  · obtain ⟨x, s, hocc, hlit, huniq⟩ := hν.1 c hc
    refine ⟨Occ.real c x s hocc, ⟨(hubOf_eq_inl_iff _ _).mpr rfl, mem_ofModel.mpr hlit⟩,
      fun o ⟨hoh, ho⟩ => ?_⟩
    have hoc : o.c = c := (hubOf_eq_inl_iff o ⟨c, hc⟩).mp hoh
    obtain ⟨hx, hs⟩ := huniq o.x o.s (o.occIn_of_coe hoc) (mem_ofModel.mp ho)
    exact Occ.ext hoc hx hs
  · refine ⟨Occ.dummy x hx (decide (ν x)), ⟨(hubOf_eq_inr_iff _ _).mpr ⟨rfl, rfl⟩, ?_⟩,
      fun o ⟨hoh, ho⟩ => ?_⟩
    · rw [mem_ofModel]
      by_cases h : ν x
      · simp [Occ.dummy, Occ.x, Occ.s, LitTrue, h]
      · simp [Occ.dummy, Occ.x, Occ.s, LitTrue, h]
    · obtain ⟨hob, hox⟩ := (hubOf_eq_inr_iff o ⟨x, hx⟩).mp hoh
      refine Occ.ext hob hox ?_
      have hlit := mem_ofModel.mp ho
      rw [hox] at hlit
      cases hs : o.s
      · rw [hs] at hlit
        simp only [LitTrue, Bool.false_eq_true, ↓reduceIte] at hlit
        simp [Occ.dummy, Occ.s, hlit]
      · rw [hs] at hlit
        simp only [LitTrue, ↓reduceIte] at hlit
        simp [Occ.dummy, Occ.s, hlit]

/-- **The consistent choices are the exactly-one models.** -/
noncomputable def consistentEquiv :
    {U : Finset (Occ A) // Consistent U} ≃ {ν : A → Prop // OneInModel A ν} where
  toFun U := ⟨toModel U.1, oneInModel_toModel U.2⟩
  invFun ν := ⟨ofModel ν.1, consistent_ofModel ν.2⟩
  left_inv U := Subtype.ext (Finset.ext fun o => by
    rw [mem_ofModel, litTrue_toModel_iff U.2])
  right_inv ν := Subtype.ext (funext fun x => propext ⟨fun ⟨_, h⟩ => mem_ofModel.mp h,
    fun h => ⟨ν.2.2 x h, mem_ofModel.mpr h⟩⟩)

open Classical in
/-- The number of consistent choices is the number of exactly-one models. -/
theorem card_consistent :
    ((univ : Finset (Finset (Occ A))).filter Consistent).card =
      Nat.card {ν : A → Prop // OneInModel A ν} := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_congr consistentEquiv]

/-- **The permanent of the base graph with the gadgets attached is `4` to the
number of occurrences times the number of exactly-one models.** -/
theorem bperm_attachAll_sites_eq :
    bperm (Site.attachAll baseM (sites (A := A))) =
      4 ^ Fintype.card (Occ A) * (SharpOneInSAT A : ℤ) := by
  rw [bperm_attachAll_sites, card_consistent, sharpOneInSat_apply]

end SatCover

end DescriptiveComplexity
