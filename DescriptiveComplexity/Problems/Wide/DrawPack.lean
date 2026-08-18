/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawSpec
import DescriptiveComplexity.Problems.Wide.DrawData

/-!
# Padding a prefix normal form

`DescriptiveComplexity.Draw.exists_prenexPack` puts every formula into the prefix
normal form the program's control is built from, but it puts it in the *shortest*
one: a quantifier-free sentence gets a pack with no levels at all. The reduction
cannot live with that – its address blocks are `Fin ko ⊕ₗ Fin ki`, and a step
definition all of whose variables are nullary and all of whose packs are
quantifier-free leaves that type **empty**, which is exactly the hypothesis
`reaches_mainB` spends. So the packs are padded rather than cased on.

Padding is one vacuous innermost level: the matrix is lifted past a new bound
variable it does not mention, and the prefix walks one step further. The whole
content is `DescriptiveComplexity.Draw.altQuantFrom_liftLast` – a prefix over a
predicate that ignores its last coordinate is the prefix without it – whose
`Nonempty` hypothesis is what makes the new level vacuous in *both* polarities.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language

/-! ### A vacuous innermost level -/

section Vacuous

variable {A : Type} [Nonempty A] {n : ℕ} {pol : ℕ → Bool} {P : (Fin n → A) → Prop}

omit [Nonempty A] in
/-- Updating a coordinate the shorter valuation still has commutes with
forgetting the last one. -/
private theorem update_comp_castSucc {j : ℕ} (hj : j < n) (v : Fin (n + 1) → A) (a : A) :
    (Function.update v ⟨j, Nat.lt_succ_of_lt hj⟩ a) ∘ Fin.castSucc =
      Function.update (v ∘ Fin.castSucc) ⟨j, hj⟩ a := by
  funext i
  by_cases hi : (i : ℕ) = j
  · have h2 : i = (⟨j, hj⟩ : Fin n) := Fin.ext hi
    rw [h2, Function.update_self]
    exact Function.update_self _ a v
  · have h1 : Fin.castSucc i ≠ (⟨j, Nat.lt_succ_of_lt hj⟩ : Fin (n + 1)) := fun h =>
      hi (congrArg Fin.val h)
    have h2 : i ≠ (⟨j, hj⟩ : Fin n) := fun h => hi (congrArg Fin.val h)
    simp only [Function.comp_apply, Function.update_of_ne h1, Function.update_of_ne h2]

omit [Nonempty A] in
/-- Updating the *new* coordinate is invisible to the shorter valuation. -/
private theorem update_last_comp_castSucc (v : Fin (n + 1) → A) (a : A) :
    (Function.update v (Fin.last n) a) ∘ Fin.castSucc = v ∘ Fin.castSucc := by
  funext i
  simp only [Function.comp_apply]
  exact Function.update_of_ne (Fin.castSucc_lt_last i).ne a v

/-- **A prefix over a predicate that ignores its last coordinate is the prefix
without it.** The new level is vacuous whichever polarity it is given, the
universe being nonempty. -/
theorem altQuantFrom_liftLast :
    ∀ (r j : ℕ), n ≤ j + r → ∀ v : Fin (n + 1) → A,
      (altQuantFrom pol (fun w : Fin (n + 1) → A => P (w ∘ Fin.castSucc)) j v ↔
        altQuantFrom pol P j (v ∘ Fin.castSucc)) := by
  intro r
  induction r with
  | zero =>
    intro j hj v
    rw [altQuantFrom_of_le (P := P) (by omega)]
    rcases Nat.lt_or_ge n j with hlt | hge
    · rw [altQuantFrom_of_le (P := fun w : Fin (n + 1) → A => P (w ∘ Fin.castSucc))
        (by omega)]
    · have hjn : j = n := by omega
      subst hjn
      have hlast : (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1)) = Fin.last j := rfl
      rcases hp : pol j with _ | _
      · rw [altQuantFrom_all (P := fun w : Fin (j + 1) → A => P (w ∘ Fin.castSucc))
          (Nat.lt_succ_self j) hp]
        simp only [hlast, altQuantFrom_of_le (P := fun w : Fin (j + 1) → A =>
          P (w ∘ Fin.castSucc)) (le_refl (j + 1)), update_last_comp_castSucc]
        exact ⟨fun h => h (Classical.arbitrary A), fun h _ => h⟩
      · rw [altQuantFrom_ex (P := fun w : Fin (j + 1) → A => P (w ∘ Fin.castSucc))
          (Nat.lt_succ_self j) hp]
        simp only [hlast, altQuantFrom_of_le (P := fun w : Fin (j + 1) → A =>
          P (w ∘ Fin.castSucc)) (le_refl (j + 1)), update_last_comp_castSucc]
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨Classical.arbitrary A, h⟩⟩
  | succ r ih =>
    intro j hj v
    rcases Nat.lt_or_ge j n with hlt | hge
    · rcases hp : pol j with _ | _
      · rw [altQuantFrom_all (P := fun w : Fin (n + 1) → A => P (w ∘ Fin.castSucc))
          (Nat.lt_succ_of_lt hlt) hp, altQuantFrom_all (P := P) hlt hp]
        refine forall_congr' fun a => ?_
        rw [ih (j + 1) (by omega), update_comp_castSucc hlt]
      · rw [altQuantFrom_ex (P := fun w : Fin (n + 1) → A => P (w ∘ Fin.castSucc))
          (Nat.lt_succ_of_lt hlt) hp, altQuantFrom_ex (P := P) hlt hp]
        refine exists_congr fun a => ?_
        rw [ih (j + 1) (by omega), update_comp_castSucc hlt]
    · exact ih j (by omega) v

end Vacuous

/-! ### One more level -/

section Succ

variable {M : Language.{0, 0}} {k : ℕ} {φ : M.Formula (Fin k)}

/-- **A prefix normal form with one more level**: the matrix lifted past a new
innermost variable it does not mention. Iterating it puts any pack above any
level count, which is how the reduction's block index is kept nonempty. -/
noncomputable def PrenexPack.succ (pk : PrenexPack φ) : PrenexPack φ where
  n := pk.n + 1
  kLe := Nat.le_succ_of_le pk.kLe
  pol := pk.pol
  mat := pk.mat.liftAt 1 pk.n
  isQF := pk.isQF.liftAt
  spec := by
    intro A _ _ v xs hagree
    have hlift : ∀ w : Fin (pk.n + 1) → A,
        (pk.mat.liftAt 1 pk.n).Realize (default : Empty → A) w ↔
          pk.mat.Realize default (w ∘ Fin.castSucc) := by
      intro w
      rw [BoundedFormula.realize_liftAt (by omega)]
      refine iff_of_eq (congrArg _ (funext fun i => ?_))
      simp only [Function.comp_apply]
      rw [if_pos i.isLt]
      rfl
    refine (pk.spec A (v ∘ Fin.castSucc) xs fun i => ?_).trans ?_
    · rw [hagree i]
      rfl
    · refine (altQuantFrom_liftLast (P := fun w => pk.mat.Realize default w)
        (pk.n + 1) k (by omega) v).symm.trans ?_
      exact iff_of_eq (congrArg (fun Q => altQuantFrom pk.pol Q k v)
        (funext fun w => propext (hlift w).symm))

/-- The padded pack has one more level. -/
@[simp] theorem PrenexPack.succ_n (pk : PrenexPack φ) : pk.succ.n = pk.n + 1 := rfl

end Succ

/-! ### The encoding layout, and the record a source is packed into -/

section Source

variable {L : Language.{0, 0}} (X : ExpExpansion L)

/-- **The encoding budget**: one coordinate per component of the one-hot code,
one per payload position, and nothing else. -/
noncomputable def encDim : ℕ := Nat.card (PtCode X) + blockArityBound X.B

variable {X}

/-- The code components, numbered. -/
noncomputable def ptFin : PtCode X ≃ Fin (Nat.card (PtCode X)) :=
  letI := Fintype.ofFinite (PtCode X)
  (Fintype.equivFin (PtCode X)).trans (finCongr Nat.card_eq_fintype_card.symm)

/-- **The standard layout**: the code in the first coordinates, the payload
right after it, both read off `DescriptiveComplexity.Draw.ptFin`. -/
noncomputable def stdLayout {dd : ℕ} (h : encDim X ≤ dd) :
    EncLayout (PtCode X) (blockArityBound X.B) dd where
  cIx q := ⟨(ptFin (X := X) q : ℕ), by
    have := (ptFin (X := X) q).isLt
    rw [encDim] at h
    omega⟩
  pIx p := ⟨Nat.card (PtCode X) + (p : ℕ), by
    have := p.isLt
    rw [encDim] at h
    omega⟩
  cInj q q' hq := by
    have h2 := congrArg Fin.val hq
    simp only at h2
    exact (ptFin (X := X)).injective (Fin.ext h2)
  pInj p p' hp := Fin.ext (by have := congrArg Fin.val hp; simpa using this)
  disj q p hqp := by
    have h1 := (ptFin (X := X) q).isLt
    have h2 := congrArg Fin.val hqp
    simp only at h2
    omega

/-- The layout inhabits the budget: every coordinate it names is below
`encDim`. -/
theorem stdLayout_lt {dd : ℕ} (h : encDim X ≤ dd) (j : Fin dd)
    (hj : (∃ q : PtCode X, (stdLayout h).cIx q = j) ∨
      ∃ p : Fin (blockArityBound X.B), (stdLayout h).pIx p = j) :
    (j : ℕ) < encDim X := by
  rcases hj with ⟨q, hq⟩ | ⟨p, hp⟩
  · have h1 := (ptFin (X := X) q).isLt
    have h2 := congrArg Fin.val hq
    simp only [stdLayout] at h2
    rw [encDim]
    omega
  · have h1 := p.isLt
    have h2 := congrArg Fin.val hp
    simp only [stdLayout] at h2
    rw [encDim]
    omega

/-- **A source packed into a `DescriptiveComplexity.Draw.Data`**: the prenex
packs of every formula the program evaluates, each padded by one level so that
the block index is nonempty, and the standard layout at a dimension the caller
chooses. -/
noncomputable def Data.ofSource (X : ExpExpansion L)
    (d : StepDef (X.E.sum Language.order)) {dd : ℕ} (hdd : encDim X ≤ dd) :
    Data L where
  X := X
  d := d
  pk i := (Classical.choice (exists_prenexPack (d.step i))).succ
  pkOut := (Classical.choice
    (exists_prenexPack (d.out.relabel (Empty.elim : Empty → Fin 0)))).succ
  domPk t := Classical.choice
    (exists_prenexPack ((X.dom t).relabel (Empty.elim : Empty → Fin 0)))
  relPk r τ := Classical.choice
    (exists_prenexPack ((X.relSentence r τ).relabel (Empty.elim : Empty → Fin 0)))
  dd0 := encDim X
  dd := dd
  ly := stdLayout hdd
  lyLt := stdLayout_lt hdd
  dd0Le := hdd

/-- The packed record's block index is nonempty: the output pack was padded. -/
theorem Data.ki_pos (X : ExpExpansion L) (d : StepDef (X.E.sum Language.order))
    {dd : ℕ} (hdd : encDim X ≤ dd) : 0 < (Data.ofSource X d hdd).ki :=
  lt_of_lt_of_le (Nat.succ_pos _) ((Data.ofSource X d hdd).nOf_le_ki none)

end Source

end Draw

end DescriptiveComplexity
