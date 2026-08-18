/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.AltQuant

/-!
# Relativizing an alternating prefix along an encoding

The quantifiers of a step formula of the EXPSPACE reduction range over the
*points* of an exponential expansion, but the enumeration a wide machine can
run – the binary increment of a register – ranges over all the **block values**
of an address, most of which encode no point at all. This file is the bridge:
an alternating prefix over a type is the same prefix over any type it embeds
into, provided the matrix is **gated** – each existentially quantified
coordinate is required to be an encoding, each universally quantified one is
excused when it is not, and the matrix proper is read at the decoded values.

`DescriptiveComplexity.Draw.gateMat` is the gated matrix and
`DescriptiveComplexity.Draw.altQuantFrom_gateMat` the equivalence. The two
absorption lemmas it rests on say what a valuation with a garbage coordinate is
worth: a garbage coordinate under an existential polarity kills its subtree
(`DescriptiveComplexity.Draw.not_altQuantFrom_gateMat_of_bad_ex`), one under a
universal polarity satisfies it outright
(`DescriptiveComplexity.Draw.altQuantFrom_gateMat_of_bad_all`) – which is
exactly the standard relativization `(∃x φ)^G = ∃x (G x ∧ φ^G)`,
`(∀x φ)^G = ∀x (G x → φ^G)`, pushed through a prenex prefix in one pass.

Everything is stated for an arbitrary injection with image `G`, so the same
lemma serves the point encodings of the reduction and the singleton encodings
of its element loops.
-/

namespace DescriptiveComplexity

namespace Draw

section Gate

variable {α β : Type} [Nonempty α] (e : α → β) (G : β → Prop) {n : ℕ} (pol : ℕ → Bool)

/-- **The gated matrix**: every existentially quantified coordinate must be an
encoding, and provided every universally quantified one is too, the matrix is
read at the decoded values. Coordinates that are encodings pass their gates
whatever their polarity, so a valuation wholly inside the image satisfies the
gated matrix exactly when its decoding satisfies the matrix. -/
noncomputable def gateMat (P : (Fin n → α) → Prop) : (Fin n → β) → Prop := fun w =>
  (∀ i : Fin n, pol (i : ℕ) = true → G (w i)) ∧
    ((∀ i : Fin n, pol (i : ℕ) = false → G (w i)) → P fun i => Function.invFun e (w i))

variable {e G pol}

omit [Nonempty α] in
/-- Updating an encoded valuation at an encoded value is encoding the updated
valuation. -/
theorem update_encode (v : Fin n → α) (k : Fin n) (a : α) :
    Function.update (fun i => e (v i)) k (e a) = fun i => e (Function.update v k a i) := by
  refine funext fun i => ?_
  by_cases hik : i = k
  · subst hik
    simp
  · simp [hik]

variable {P : (Fin n → α) → Prop}

/-- A coordinate index strictly below a level is not the level's own
coordinate. -/
private theorem ne_of_lt_level {i₀ : Fin n} {j : ℕ} (hij : (i₀ : ℕ) < j) (hjn : j < n) :
    i₀ ≠ ⟨j, hjn⟩ := fun hc => by
  rw [hc] at hij
  exact absurd hij (lt_irrefl j)

/-- **A garbage coordinate under an existential polarity kills its subtree**:
if some coordinate already chosen fails its gate and its polarity is
existential, no way of playing the remaining prefix satisfies the gated
matrix. -/
theorem not_altQuantFrom_gateMat_of_bad_ex {i₀ : Fin n} (hpol : pol (i₀ : ℕ) = true)
    {j : ℕ} (hij : (i₀ : ℕ) < j) {w : Fin n → β} (hG : ¬G (w i₀)) :
    ¬altQuantFrom pol (gateMat e G pol P) j w := by
  have hβ : Nonempty β := ⟨e (Classical.arbitrary α)⟩
  have key : ∀ (r j : ℕ) (w : Fin n → β), n - j ≤ r → (i₀ : ℕ) < j → ¬G (w i₀) →
      ¬altQuantFrom pol (gateMat e G pol P) j w := by
    intro r
    induction r with
    | zero =>
      intro j w hr hij hG
      rw [altQuantFrom_of_le (by omega)]
      exact fun hc => hG (hc.1 i₀ hpol)
    | succ r ih =>
      intro j w hr hij hG
      by_cases hjn : j < n
      · have hup : ∀ b : β, ¬altQuantFrom pol (gateMat e G pol P) (j + 1)
            (Function.update w ⟨j, hjn⟩ b) := fun b => by
          refine ih (j + 1) _ (by omega) (by omega) ?_
          rwa [Function.update_of_ne (ne_of_lt_level hij hjn)]
        by_cases hp : pol j = true
        · rw [altQuantFrom_ex hjn hp]
          rintro ⟨b, hb⟩
          exact hup b hb
        · rw [altQuantFrom_all hjn (by simpa using hp)]
          intro hc
          obtain ⟨b⟩ := hβ
          exact hup b (hc b)
      · rw [altQuantFrom_of_le (by omega)]
        exact fun hc => hG (hc.1 i₀ hpol)
  exact key _ j w le_rfl hij hG

/-- **A garbage coordinate under a universal polarity satisfies its subtree
outright**, provided every existentially quantified coordinate already chosen
is an encoding: the gated matrix's implication is vacuous at every leaf below
this valuation. -/
theorem altQuantFrom_gateMat_of_bad_all (hbij : ∀ b, G b ↔ ∃ a, e a = b)
    {i₀ : Fin n} (hpol : pol (i₀ : ℕ) = false) {j : ℕ} (hij : (i₀ : ℕ) < j)
    {w : Fin n → β} (hG : ¬G (w i₀))
    (hval : ∀ i : Fin n, (i : ℕ) < j → pol (i : ℕ) = true → G (w i)) :
    altQuantFrom pol (gateMat e G pol P) j w := by
  have key : ∀ (r j : ℕ) (w : Fin n → β), n - j ≤ r → (i₀ : ℕ) < j → ¬G (w i₀) →
      (∀ i : Fin n, (i : ℕ) < j → pol (i : ℕ) = true → G (w i)) →
      altQuantFrom pol (gateMat e G pol P) j w := by
    intro r
    induction r with
    | zero =>
      intro j w hr hij hG hval
      rw [altQuantFrom_of_le (by omega)]
      exact ⟨fun i hi => hval i (by omega) hi, fun hc => absurd (hc i₀ hpol) hG⟩
    | succ r ih =>
      intro j w hr hij hG hval
      by_cases hjn : j < n
      · have hne := ne_of_lt_level hij hjn
        have hval' : ∀ b : β, G b →
            ∀ i : Fin n, (i : ℕ) < j + 1 → pol (i : ℕ) = true →
              G (Function.update w ⟨j, hjn⟩ b i) := by
          intro b hb i hi hpi
          by_cases hik : i = ⟨j, hjn⟩
          · subst hik
            rwa [Function.update_self]
          · rw [Function.update_of_ne hik]
            refine hval i ?_ hpi
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
            · exact h
            · exact absurd (Fin.ext h) hik
        by_cases hp : pol j = true
        · rw [altQuantFrom_ex hjn hp]
          refine ⟨e (Classical.arbitrary α), ?_⟩
          refine ih (j + 1) _ (by omega) (by omega) ?_
            (hval' _ ((hbij _).mpr ⟨_, rfl⟩))
          rwa [Function.update_of_ne hne]
        · rw [altQuantFrom_all hjn (by simpa using hp)]
          intro b
          have hvb : ∀ i : Fin n, (i : ℕ) < j + 1 → pol (i : ℕ) = true →
              G (Function.update w ⟨j, hjn⟩ b i) := by
            intro i hi hpi
            by_cases hik : i = ⟨j, hjn⟩
            · subst hik
              rw [show ((⟨j, hjn⟩ : Fin n) : ℕ) = j from rfl] at hpi
              exact absurd hpi hp
            · rw [Function.update_of_ne hik]
              refine hval i ?_ hpi
              rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
              · exact h
              · exact absurd (Fin.ext h) hik
          refine ih (j + 1) _ (by omega) (by omega) ?_ hvb
          rwa [Function.update_of_ne hne]
      · rw [altQuantFrom_of_le (by omega)]
        exact ⟨fun i hi => hval i (by omega) hi, fun hc => absurd (hc i₀ hpol) hG⟩
  exact key _ j w le_rfl hij hG hval

/-- **Relativization along an encoding**: an alternating prefix over a type is
the same prefix over the encodings, with the gated matrix. This is what moves a
step formula's quantifiers from the points of the expansion to the block values
a register enumerates. -/
theorem altQuantFrom_gateMat (hinj : Function.Injective e)
    (hbij : ∀ b, G b ↔ ∃ a, e a = b) {j : ℕ} (v : Fin n → α) :
    altQuantFrom pol (gateMat e G pol P) j (fun i => e (v i)) ↔ altQuantFrom pol P j v := by
  have key : ∀ (r j : ℕ) (v : Fin n → α), n - j ≤ r →
      (altQuantFrom pol (gateMat e G pol P) j (fun i => e (v i)) ↔
        altQuantFrom pol P j v) := by
    intro r
    induction r with
    | zero =>
      intro j v hr
      rw [altQuantFrom_of_le (by omega), altQuantFrom_of_le (by omega)]
      have hdec : (fun i => Function.invFun e (e (v i))) = v :=
        funext fun i => Function.leftInverse_invFun hinj (v i)
      simp only [gateMat]
      rw [hdec]
      exact ⟨fun hc => hc.2 fun i _ => (hbij _).mpr ⟨v i, rfl⟩,
        fun hc => ⟨fun i _ => (hbij _).mpr ⟨v i, rfl⟩, fun _ => hc⟩⟩
    | succ r ih =>
      intro j v hr
      by_cases hjn : j < n
      · by_cases hp : pol j = true
        · rw [altQuantFrom_ex hjn hp, altQuantFrom_ex hjn hp]
          constructor
          · rintro ⟨b, hb⟩
            by_cases hGb : G b
            · obtain ⟨a, rfl⟩ := (hbij b).mp hGb
              refine ⟨a, ?_⟩
              rw [update_encode] at hb
              exact (ih (j + 1) _ (by omega)).mp hb
            · refine absurd hb (not_altQuantFrom_gateMat_of_bad_ex (i₀ := ⟨j, hjn⟩) hp
                (Nat.lt_succ_self j) ?_)
              rwa [Function.update_self]
          · rintro ⟨a, ha⟩
            refine ⟨e a, ?_⟩
            rw [update_encode]
            exact (ih (j + 1) _ (by omega)).mpr ha
        · have hp' : pol j = false := by simpa using hp
          rw [altQuantFrom_all hjn hp', altQuantFrom_all hjn hp']
          constructor
          · intro hall a
            have hb := hall (e a)
            rw [update_encode] at hb
            exact (ih (j + 1) _ (by omega)).mp hb
          · intro hall b
            by_cases hGb : G b
            · obtain ⟨a, rfl⟩ := (hbij b).mp hGb
              rw [update_encode]
              exact (ih (j + 1) _ (by omega)).mpr (hall a)
            · refine altQuantFrom_gateMat_of_bad_all (i₀ := ⟨j, hjn⟩) hbij hp'
                (Nat.lt_succ_self j) ?_ fun i hi hpi => ?_
              · rwa [Function.update_self]
              · by_cases hik : i = ⟨j, hjn⟩
                · subst hik
                  rw [show ((⟨j, hjn⟩ : Fin n) : ℕ) = j from rfl] at hpi
                  exact absurd hpi hp
                · rw [Function.update_of_ne hik]
                  exact (hbij _).mpr ⟨v i, rfl⟩
      · rw [altQuantFrom_of_le (by omega), altQuantFrom_of_le (by omega)]
        have hdec : (fun i => Function.invFun e (e (v i))) = v :=
          funext fun i => Function.leftInverse_invFun hinj (v i)
        simp only [gateMat]
        rw [hdec]
        exact ⟨fun hc => hc.2 fun i _ => (hbij _).mpr ⟨v i, rfl⟩,
          fun hc => ⟨fun i _ => (hbij _).mpr ⟨v i, rfl⟩, fun _ => hc⟩⟩
  exact key _ j v le_rfl

end Gate

end Draw

end DescriptiveComplexity
