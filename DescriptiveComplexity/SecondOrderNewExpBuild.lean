/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.SecondOrderNewExpPull
import DescriptiveComplexity.SecondOrderNewExp

/-!
# The guess the forward direction makes

`DescriptiveComplexity.SecondOrderNewExpPull` reads an assignment of the guessed
block as a naming of the points of an exponential expansion. This file goes the
other way: given a linear order of the instance and an assignment of the source
problem's block over the expansion, it *builds* the assignment of the guessed
block that the sentence asks for, one invented value per assignment of the
tagged block, and checks every guard.

The value naming an assignment is fixed by an arbitrary enumeration of the
assignments; the meaning variables then say “this tuple of original elements
belongs to that value's assignment”, the order variable says “both entries are
original and the first is below the second”, and the source problem's variables
say “these values name points the certificate relates”. Nothing here is a
choice: the guards pin the guess down to exactly this, up to which value gets
which assignment.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure ExpExpansion

variable {L : Language.{0, 0}} [L.IsRelational] {X : ExpExpansion L} {C : SOBlock}
variable {A : Type} [L.Structure A] [LinearOrder A] {m : ℕ}

/-! ### The guess -/

variable (σ : C.Assignment (X.Map A)) (enum : Fin m ≃ (taggedBlock X).Assignment A)

/-- **The assignment the forward direction guesses**: the order of the instance,
one invented value per assignment of the tagged block, and the certificate read
at the values naming the points. -/
noncomputable def buildAssign : (pullBlock X C).Assignment (A ⊕ Fin m) := fun idx =>
  match idx with
  | Sum.inl () => fun w => ∃ a b : A,
      w = (![Sum.inl a, Sum.inl b] : Fin 2 → A ⊕ Fin m) ∧ a ≤ b
  | Sum.inr (Sum.inl i) => fun u => ∃ (k : Fin m) (ts : Fin ((taggedBlock X).arity i) → A),
      u = (Fin.cases (Sum.inr k) fun j => Sum.inl (ts j) :
        Fin ((taggedBlock X).arity i + 1) → A ⊕ Fin m) ∧ enum k i ts
  | Sum.inr (Sum.inr j) => fun w => ∃ ps : Fin (C.arity j) → X.Map A,
      (∀ l, w l = Sum.inr (enum.symm (pointAssign (ps l)))) ∧ σ j ps

/-! ### What the meaning variables say -/

private theorem fin_cases_inj {M : Type} {n : ℕ} {v v' : M} {w w' : Fin n → M}
    (h : (Fin.cases v w : Fin (n + 1) → M) = Fin.cases v' w') : v = v' ∧ w = w' := by
  refine ⟨?_, funext fun j => ?_⟩
  · simpa using congrFun h 0
  · have hj := congrFun h j.succ
    rwa [Fin.cases_succ, Fin.cases_succ] at hj

omit [L.IsRelational] in
theorem meaningOfB_build (i : (taggedBlock X).ι) (v : A ⊕ Fin m)
    (w : Fin ((taggedBlock X).arity i) → A ⊕ Fin m) :
    meaningOfB (pullMeanPart (buildAssign σ enum)) i v w ↔
      ∃ (k : Fin m) (ts : Fin ((taggedBlock X).arity i) → A),
        v = Sum.inr k ∧ (∀ j, w j = Sum.inl (ts j)) ∧ enum k i ts := by
  constructor
  · rintro ⟨k, ts, hu, hk⟩
    obtain ⟨hv, hw⟩ := fin_cases_inj hu
    exact ⟨k, ts, hv, fun j => congrFun hw j, hk⟩
  · rintro ⟨k, ts, rfl, hw, hk⟩
    refine ⟨k, ts, funext fun j => ?_, hk⟩
    induction j using Fin.cases with
    | zero => rfl
    | succ j => rw [Fin.cases_succ]; exact hw j

omit [L.IsRelational] in
theorem meanAtB_build (k : Fin m) (i : (taggedBlock X).ι)
    (ts : Fin ((taggedBlock X).arity i) → A) :
    meanAtB (pullMeanPart (buildAssign σ enum)) k ⟨i, ts⟩ ↔ enum k i ts := by
  rw [meanAtB, meaningOfB_build]
  constructor
  · rintro ⟨k', ts', hk, hts, h⟩
    obtain rfl : k = k' := Sum.inr_injective hk
    obtain rfl : ts = ts' := funext fun j => Sum.inl_injective (hts j)
    exact h
  · exact fun h => ⟨k, ts, rfl, fun _ => rfl, h⟩

omit [L.IsRelational] in
theorem bijective_meanAtB_build :
    Function.Bijective (meanAtB (pullMeanPart (buildAssign σ enum))) := by
  have hfun : meanAtB (pullMeanPart (buildAssign σ enum)) =
      fun k p => enum k p.1 p.2 :=
    funext fun k => funext fun p => propext (meanAtB_build σ enum k p.1 p.2)
  rw [hfun]
  exact ((SOBlock.assignEquivSigma (taggedBlock X) A).symm.trans enum.symm).symm.bijective

/-! ### The meaning guards -/

omit [L.IsRelational] in
theorem meaningOfB_build_inl (i : (taggedBlock X).ι) (k : Fin m)
    (b : Fin ((taggedBlock X).arity i) → A) :
    meaningOfB (pullMeanPart (buildAssign σ enum)) i (Sum.inr k) (fun j => Sum.inl (b j)) ↔
      enum k i b :=
  meanAtB_build σ enum k i b

omit [L.IsRelational] in
theorem not_meaningOfB_build (i : (taggedBlock X).ι) (v : A ⊕ Fin m)
    (w : Fin ((taggedBlock X).arity i) → A ⊕ Fin m) (hnot : ¬∀ j, IsOld (w j)) :
    ¬meaningOfB (pullMeanPart (buildAssign σ enum)) i v w := by
  intro hM
  obtain ⟨k, ts, -, hw, -⟩ := (meaningOfB_build σ enum i v w).mp hM
  exact hnot fun j => (hw j).symm ▸ isOld_inl (m := m) (ts j)

omit [L.IsRelational] in
/-- A meaning of the built guess relates an invented value to original elements
and nothing else. -/
theorem build_shaped (i : (taggedBlock X).ι) (v : A ⊕ Fin m)
    (w : Fin ((taggedBlock X).arity i) → A ⊕ Fin m)
    (hM : meaningOfB (pullMeanPart (buildAssign σ enum)) i v w) :
    ¬IsOld v ∧ ∀ j, IsOld (w j) := by
  obtain ⟨k, ts, rfl, hw, -⟩ := (meaningOfB_build σ enum i v w).mp hM
  exact ⟨not_isOld_inr k, fun j => (hw j).symm ▸ isOld_inl (m := m) (ts j)⟩

omit [L.IsRelational] in
/-- Some invented value of the built guess means the empty assignment. -/
theorem build_empty : ∃ v : A ⊕ Fin m, ¬IsOld v ∧
    ∀ (i : (taggedBlock X).ι) (w : Fin ((taggedBlock X).arity i) → A ⊕ Fin m),
      ¬meaningOfB (pullMeanPart (buildAssign σ enum)) i v w := by
  refine ⟨Sum.inr (enum.symm fun _ _ => False), not_isOld_inr _, fun i w hM => ?_⟩
  obtain ⟨k, ts, hk, -, hval⟩ := (meaningOfB_build σ enum i _ w).mp hM
  obtain rfl : enum.symm (fun _ _ => False) = k := Sum.inr_injective hk
  exact (congrFun (congrFun (enum.apply_symm_apply fun _ _ => False) i) ts) ▸ hval

omit [L.IsRelational] in
/-- Invented values of the built guess agreeing on every variable are equal. -/
theorem build_inj (v u : A ⊕ Fin m) (hv : ¬IsOld v) (hu : ¬IsOld u)
    (hM : ∀ (i : (taggedBlock X).ι) (w : Fin ((taggedBlock X).arity i) → A ⊕ Fin m),
      meaningOfB (pullMeanPart (buildAssign σ enum)) i v w ↔
        meaningOfB (pullMeanPart (buildAssign σ enum)) i u w) :
    v = u := by
  obtain ⟨k, rfl⟩ : ∃ k : Fin m, v = Sum.inr k := by
    cases v with
    | inl a => exact absurd (isOld_inl (m := m) a) hv
    | inr k => exact ⟨k, rfl⟩
  obtain ⟨k', rfl⟩ : ∃ k' : Fin m, u = Sum.inr k' := by
    cases u with
    | inl a => exact absurd (isOld_inl (m := m) a) hu
    | inr k' => exact ⟨k', rfl⟩
  refine congrArg Sum.inr (enum.injective (funext fun i => funext fun b => propext ?_))
  exact ((meaningOfB_build_inl σ enum i k b).symm.trans (hM i _)).trans
    (meaningOfB_build_inl σ enum i k' b)

open Classical in
omit [L.IsRelational] in
/-- Flipping one tuple of one variable of the built guess lands on an invented
value again, the other variables unchanged. -/
theorem build_flip (i : (taggedBlock X).ι) (v : A ⊕ Fin m)
    (y : Fin ((taggedBlock X).arity i) → A ⊕ Fin m) (hv : ¬IsOld v)
    (hy : ∀ j, IsOld (y j)) :
    ∃ u : A ⊕ Fin m, ¬IsOld u ∧
      (∀ w : Fin ((taggedBlock X).arity i) → A ⊕ Fin m,
        meaningOfB (pullMeanPart (buildAssign σ enum)) i u w ↔
          (meaningOfB (pullMeanPart (buildAssign σ enum)) i v w ↔ ¬∀ j, w j = y j)) ∧
      ∀ i' : (taggedBlock X).ι, i' ≠ i →
        ∀ w : Fin ((taggedBlock X).arity i') → A ⊕ Fin m,
          meaningOfB (pullMeanPart (buildAssign σ enum)) i' u w ↔
            meaningOfB (pullMeanPart (buildAssign σ enum)) i' v w := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k : Fin m, v = Sum.inr k := by
    cases v with
    | inl a => exact absurd (isOld_inl (m := m) a) hv
    | inr k => exact ⟨k, rfl⟩
  have hy' : ∀ j, ∃ b : A, y j = Sum.inl b := fun j => by
    cases hj : y j with
    | inl b => exact ⟨b, rfl⟩
    | inr c => exact absurd (hj ▸ hy j) (not_isOld_inr c)
  choose a ha using hy'
  have hup : ∀ (α : (taggedBlock X).Assignment A) (i' : (taggedBlock X).ι)
      (c : Fin ((taggedBlock X).arity i') → A), enum (enum.symm α) i' c = α i' c :=
    fun α i' c => congrFun (congrFun (enum.apply_symm_apply α) i') c
  obtain ⟨α, hself, hne⟩ : ∃ α : (taggedBlock X).Assignment A,
      (∀ c, α i c ↔ (enum k i c ↔ ¬∀ j, c j = a j)) ∧
        ∀ i'' : (taggedBlock X).ι, i'' ≠ i → α i'' = enum k i'' :=
    ⟨Function.update (enum k) i fun c => (enum k i c ↔ ¬∀ j, c j = a j),
      fun c => iff_of_eq (congrFun (Function.update_self i _ (enum k)) c),
      fun i'' hii => Function.update_of_ne hii _ (enum k)⟩
  refine ⟨Sum.inr (enum.symm α), not_isOld_inr _, fun w => ?_, fun i' hi' w => ?_⟩
  · by_cases hall : ∀ j, IsOld (w j)
    · have hw' : ∀ j, ∃ b : A, w j = Sum.inl b := fun j => by
        cases hj : w j with
        | inl b => exact ⟨b, rfl⟩
        | inr c => exact absurd (hj ▸ hall j) (not_isOld_inr c)
      choose b hb using hw'
      have hwb : w = fun j => Sum.inl (b j) := funext hb
      subst hwb
      rw [meaningOfB_build_inl, meaningOfB_build_inl]
      refine Iff.trans (iff_of_eq (hup α i b)) (Iff.trans (hself b) ?_)
      refine iff_congr Iff.rfl (not_congr (forall_congr' fun j => ?_))
      rw [ha j]
      exact ⟨fun hj => congrArg Sum.inl hj, fun hj => Sum.inl_injective hj⟩
    · have h₁ := not_meaningOfB_build σ enum i (Sum.inr (enum.symm α)) w hall
      have h₂ := not_meaningOfB_build σ enum i (Sum.inr k) w hall
      have h₃ : ¬∀ j, w j = y j := fun hwy => hall fun j => (hwy j).symm ▸ hy j
      simp only [h₁, h₂, h₃, iff_true, not_false_iff]
  · by_cases hall : ∀ j, IsOld (w j)
    · have hw' : ∀ j, ∃ b : A, w j = Sum.inl b := fun j => by
        cases hj : w j with
        | inl b => exact ⟨b, rfl⟩
        | inr c => exact absurd (hj ▸ hall j) (not_isOld_inr c)
      choose b hb using hw'
      have hwb : w = fun j => Sum.inl (b j) := funext hb
      subst hwb
      rw [meaningOfB_build_inl, meaningOfB_build_inl]
      exact Iff.trans (iff_of_eq (hup α i' b)) (iff_of_eq (congrFun (hne i' hi') b))
    · rw [iff_iff_implies_and_implies]
      exact ⟨fun hc => absurd hc (not_meaningOfB_build σ enum i' _ w hall),
        fun hc => absurd hc (not_meaningOfB_build σ enum i' _ w hall)⟩

/-! ### The order guard -/

omit [L.IsRelational] in
theorem build_ord_iff (x y : A ⊕ Fin m) :
    buildAssign (C := C) σ enum (Sum.inl ()) ![x, y] ↔
      ∃ a b : A, x = Sum.inl a ∧ y = Sum.inl b ∧ a ≤ b := by
  constructor
  · rintro ⟨a, b, hw, hab⟩
    refine ⟨a, b, ?_, ?_, hab⟩
    · simpa using congrFun hw (0 : Fin 2)
    · simpa using congrFun hw (1 : Fin 2)
  · rintro ⟨a, b, rfl, rfl, hab⟩
    exact ⟨a, b, rfl, hab⟩

omit [L.IsRelational] in
theorem build_le_iff (a b : A) : pullLe (buildAssign (C := C) σ enum) a b ↔ a ≤ b := by
  refine (build_ord_iff σ enum _ _).trans ⟨?_, fun h => ⟨a, b, rfl, rfl, h⟩⟩
  rintro ⟨a', b', ha, hb, hab⟩
  exact (Sum.inl_injective ha) ▸ (Sum.inl_injective hb) ▸ hab

/-- The built guess satisfies the order guard. -/
theorem build_ordGuard :
    letI := (pullBlock X C).structure₁ (L := newLang L) (buildAssign σ enum)
    ((A ⊕ Fin m) ⊨ extLinearGuard L (guessBlock X C)) := by
  let := (pullBlock X C).structure₁ (L := newLang L) (buildAssign σ enum)
  have hold : ∀ x : A ⊕ Fin m, IsOld x → ∃ a : A, x = Sum.inl a := by
    intro x hx
    cases x with
    | inl a => exact ⟨a, rfl⟩
    | inr c => exact absurd hx (not_isOld_inr c)
  refine (realize_extLinearGuard A m (buildAssign σ enum)).mpr
    ⟨fun x y hxy => ?_, fun x hx => ?_, fun x y z hxy hyz => ?_, fun x y hxy hyx => ?_,
      fun x y hx hy => ?_⟩
  · obtain ⟨a, b, rfl, rfl, -⟩ := (build_ord_iff σ enum x y).mp hxy
    exact ⟨isOld_inl (m := m) a, isOld_inl (m := m) b⟩
  · obtain ⟨a, rfl⟩ := hold x hx
    exact (build_ord_iff σ enum _ _).mpr ⟨a, a, rfl, rfl, le_refl a⟩
  · obtain ⟨a, b, rfl, hb, hab⟩ := (build_ord_iff σ enum x y).mp hxy
    obtain ⟨b', c, hb', rfl, hbc⟩ := (build_ord_iff σ enum y z).mp hyz
    obtain rfl : b = b' := Sum.inl_injective (hb.symm.trans hb')
    exact (build_ord_iff σ enum _ _).mpr ⟨a, c, rfl, rfl, le_trans hab hbc⟩
  · obtain ⟨a, b, rfl, rfl, hab⟩ := (build_ord_iff σ enum x y).mp hxy
    obtain ⟨b', a', hb', ha', hba⟩ := (build_ord_iff σ enum _ _).mp hyx
    obtain rfl : b = b' := Sum.inl_injective hb'
    obtain rfl : a = a' := Sum.inl_injective ha'
    exact congrArg Sum.inl (le_antisymm hab hba)
  · obtain ⟨a, rfl⟩ := hold x hx
    obtain ⟨b, rfl⟩ := hold y hy
    rcases le_total a b with h | h
    · exact Or.inl ((build_ord_iff σ enum _ _).mpr ⟨a, b, rfl, rfl, h⟩)
    · exact Or.inr ((build_ord_iff σ enum _ _).mpr ⟨b, a, rfl, rfl, h⟩)

/-- The built guess satisfies the meaning guard. -/
theorem build_meanGuard [Finite A] :
    letI := (pullBlock X C).structure₁ (L := newLang L) (buildAssign σ enum)
    ((A ⊕ Fin m) ⊨ pullMeanGuard X C) := by
  let := (pullBlock X C).structure₁ (L := newLang L) (buildAssign σ enum)
  refine (realize_pullMeanGuard (buildAssign σ enum)).mpr ?_
  let := meanStrucB (L := L) (pullMeanPart (buildAssign σ enum))
  refine (Sentence.realize_inf (A ⊕ Fin m)).mpr ⟨(Sentence.realize_inf (A ⊕ Fin m)).mpr
    ⟨(Sentence.realize_inf (A ⊕ Fin m)).mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact (realize_meanShapedB _).mpr fun i v w hM => build_shaped σ enum i v w hM
  · exact (realize_meanEmptyB _).mpr (build_empty σ enum)
  · exact (realize_meanInjB _).mpr fun v u hv hu hM => build_inj σ enum v u hv hu hM
  · exact (realize_meanFlipB _).mpr fun i v y hv hy => build_flip σ enum i v y hv hy

/-! ### The naming, the certificate, and the sentence -/

section Forward

variable [Finite A]

omit [L.IsRelational] in
theorem meanAssignEquiv_build (k : Fin m) :
    meanAssignEquiv (pullMeanPart (buildAssign σ enum)) (bijective_meanAtB_build σ enum) k =
      enum k :=
  funext fun i => funext fun ts => propext (meanAtB_build σ enum k i ts)

omit [L.IsRelational] in
theorem meanAssignEquiv_symm_build (α : (taggedBlock X).Assignment A) :
    (meanAssignEquiv (pullMeanPart (buildAssign σ enum))
        (bijective_meanAtB_build σ enum)).symm α = enum.symm α := by
  refine enum.injective ?_
  rw [enum.apply_symm_apply]
  exact (meanAssignEquiv_build σ enum _).symm.trans (Equiv.apply_symm_apply _ α)

omit [L.IsRelational] in
theorem pullName_build (p : X.Map A) :
    pullName (buildAssign σ enum) (bijective_meanAtB_build σ enum) p =
      Sum.inr (enum.symm (pointAssign p)) :=
  congrArg Sum.inr (meanAssignEquiv_symm_build σ enum (pointAssign p))

omit [L.IsRelational] in
/-- The certificate the built guess carries is the one it was built from. -/
theorem pullCert_build :
    pullCert (buildAssign σ enum)
        (pullName (buildAssign σ enum) (bijective_meanAtB_build σ enum)) = σ := by
  funext j ts
  refine propext ⟨?_, fun h => ⟨ts, fun l => pullName_build σ enum (ts l), h⟩⟩
  rintro ⟨ps, hps, hσ⟩
  have hpt : ps = ts := funext fun l =>
    (pointAssign_injective
      (enum.symm.injective (Sum.inr_injective
        ((pullName_build σ enum (ts l)).symm.trans (hps l))))).symm
  exact hpt ▸ hσ

/-- **The built guess satisfies the sentence**: the two guards by construction,
and the kernel because the certificate it carries is the given one. -/
theorem pullSentence_forward (φ : (X.E.sum C.lang).Sentence)
    (hφ : @Sentence.Realize _ (X.Map A) (C.structure₁ (L := X.E) σ) φ) :
    letI := (pullBlock X C).structure₁ (L := newLang L) (buildAssign σ enum)
    ((A ⊕ Fin m) ⊨ pullSentence X C φ) := by
  let := (pullBlock X C).structure₁ (L := newLang L) (buildAssign σ enum)
  have hpt := pullPointOn (buildAssign σ enum) fun a b => (build_le_iff σ enum a b).symm
  have hrep := pullPointRep (buildAssign σ enum) (bijective_meanAtB_build σ enum)
    fun i v w hM => build_shaped σ enum i v w hM
  refine (Sentence.realize_inf (A ⊕ Fin m)).mpr
    ⟨(Sentence.realize_inf (A ⊕ Fin m)).mpr ⟨build_ordGuard σ enum, build_meanGuard σ enum⟩, ?_⟩
  refine (realize_pullKernel (buildAssign σ enum) hpt hrep φ).mpr
    (cast (congrArg (fun τ => @Sentence.Realize _ (X.Map A) (C.structure₁ (L := X.E) τ) φ)
      (pullCert_build σ enum).symm) hφ)

end Forward

/-! ### How many values the guess invents -/

section Count

variable (X)

omit [L.IsRelational] [L.Structure A] [LinearOrder A] in
/-- **The assignments of the tagged block are exponentially many**: one variable
per index, each a relation of arity at most the block's bound, so an assignment
is read off a set of pairs of an index and a tuple of that length. -/
theorem card_taggedAssign_le [Finite A] [Nonempty A] :
    Nat.card ((taggedBlock X).Assignment A) ≤
      2 ^ (Nat.card (taggedBlock X).ι *
        Nat.card (Fin (blockArityBound (taggedBlock X)) → A)) := by
  classical
  let := Fintype.ofFinite (taggedBlock X).ι
  let := Fintype.ofFinite A
  set d := blockArityBound (taggedBlock X) with hd
  set c := Nat.card (taggedBlock X).ι with hc
  obtain ⟨a₀⟩ := ‹Nonempty A›
  obtain ⟨ε⟩ : Nonempty ((taggedBlock X).ι ≃ Fin c) := by
    rw [hc, Nat.card_eq_fintype_card]
    exact ⟨Fintype.equivFin _⟩
  have hcard : Nat.card (((taggedBlock X).ι × (Fin d → A)) → Prop) =
      2 ^ (c * Nat.card (Fin d → A)) := by
    rw [Nat.card_congr (Equiv.curry _ _ _), Nat.card_congr
      (Equiv.arrowCongr ε (Equiv.refl ((Fin d → A) → Prop)))]
    exact card_pow (Fin d → A)
  refine le_of_le_of_eq (Nat.card_le_card_of_injective
    (fun α (q : (taggedBlock X).ι × (Fin d → A)) =>
      α q.1 fun j => q.2 (Fin.castLE (arity_le_blockArityBound (taggedBlock X) q.1) j)) ?_) hcard
  intro α β hαβ
  funext i ts
  have hw : ∀ j : Fin ((taggedBlock X).arity i),
      (fun j : Fin ((taggedBlock X).arity i) =>
        (fun l : Fin d => if h : (l : ℕ) < (taggedBlock X).arity i then ts ⟨l, h⟩ else a₀)
          (Fin.castLE (arity_le_blockArityBound (taggedBlock X) i) j)) j = ts j := by
    intro j
    simp only [Fin.castLE]
    rw [dif_pos j.2]
  have h := congrFun hαβ (i, fun l : Fin d =>
    if h : (l : ℕ) < (taggedBlock X).arity i then ts ⟨l, h⟩ else a₀)
  simpa only [funext hw] using h

end Count

end DescriptiveComplexity
