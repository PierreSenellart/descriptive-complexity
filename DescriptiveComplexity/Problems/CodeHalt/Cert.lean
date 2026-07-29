/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CodeHalt.Arith
import DescriptiveComplexity.Problems.CodeHalt.Numerals
import DescriptiveComplexity.Problems.CodeHalt.Defs

/-!
# A halting computation, read off as a finite certificate

The mathematical content of `CODEHALT ∈ RE`: the code drawn by an instance
halts on `0` exactly when a **finite** amount of data witnesses it – a numeral
segment with a linear order on it, an addition and a pairing on the segment,
the number of the code each node draws, and the value each code takes on each
argument.

## The shape of the certificate

`DescriptiveComplexity.CodeHalt.Cert` is the data and
`DescriptiveComplexity.CodeHalt.CertOK` the conditions. Every condition but the
last is a *justification* rule: each fact asserted must be derivable from
facts already asserted, by one of the rules of the object it is about. Nothing
asks the guessed relations to be *closed* under the rules – only supported by
them – and nothing needs a rank, because two things already decrease:

* the **numeral of a code**: the arguments of a `pair`, `comp`, `prec` or
  `rfind'` are numbered below it (`DescriptiveComplexity.CodeHalt.dec_pair` and
  friends), so a code's own rules appeal to strictly smaller numbers;
* the **argument** of a `prec`, which is the one rule appealing to the same
  code: it steps down along the second component of the argument.

So soundness is a plain induction on the pair (code number, argument), and the
instance is *not* asked to be a well-formed tree: a code is carried by its
number, and numbers decode unambiguously.

## Why `rfind'` has no chain

The search of an `rfind'` is stated by a **bounded universal**: the answer `v`
is a place where the argument returns `0`, and every place between the input
and `v` returns something nonzero
(`DescriptiveComplexity.CodeHalt.evaln_rfind'_spec`). A step-by-step reading
would appeal to the *same* code at a *larger* argument, which no measure
decreases along; the universal reading appeals only to the argument's code.
-/

namespace DescriptiveComplexity

namespace CodeHalt

open FirstOrder Language Structure

open Nat.Partrec.Code

/-! ### The certificate -/

/-- **A halting computation, as relations on a numeral segment.** `Le` orders
the segment; `Add` and `Pr` are addition and `Nat.pair` on it; `Dec n e` says
the node `n` of the instance draws the code numbered `e`; `Ev e x v` says the
code numbered `e` returns `v` on `x`. -/
structure Cert (A D : Type) where
  /-- The order of the numeral segment. -/
  Le : D → D → Prop
  /-- `Add x y z`: `x + y = z`. -/
  Add : D → D → D → Prop
  /-- `Pr a b p`: `⟨a, b⟩ = p`, for Cantor's pairing. -/
  Pr : D → D → D → Prop
  /-- `Dec n e`: the node `n` draws the code numbered `e`. -/
  Dec : A → D → Prop
  /-- `Ev e x v`: the code numbered `e` returns `v` on the argument `x`. -/
  Ev : D → D → D → Prop

namespace Cert

variable {A D : Type} (c : Cert A D)

/-- Strictly below, in the numeral segment. -/
def Lt (x y : D) : Prop := c.Le x y ∧ x ≠ y

/-- `q` is four times `p`. -/
def Quad (p q : D) : Prop := ∃ s, c.Add p p s ∧ c.Add s s q

/-- `e` is `q + 4`. -/
def Plus4 (q e : D) : Prop :=
  ∃ u₁ u₂ u₃, IsS c.Le q u₁ ∧ IsS c.Le u₁ u₂ ∧ IsS c.Le u₂ u₃ ∧ IsS c.Le u₃ e

/-- `e` is `q + 5`. -/
def Plus5 (q e : D) : Prop := ∃ u, c.Plus4 q u ∧ IsS c.Le u e

/-- `e` is `q + 6`. -/
def Plus6 (q e : D) : Prop := ∃ u, c.Plus5 q u ∧ IsS c.Le u e

/-- `e` is `q + 7`. -/
def Plus7 (q e : D) : Prop := ∃ u, c.Plus6 q u ∧ IsS c.Le u e

/-- `e` is the numeral `1`. -/
def IsOne (e : D) : Prop := ∃ z, IsZ c.Le z ∧ IsS c.Le z e

/-- `e` is the numeral `2`. -/
def IsTwo (e : D) : Prop := ∃ u, c.IsOne u ∧ IsS c.Le u e

/-- `e` is the numeral `3`. -/
def IsThree (e : D) : Prop := ∃ u, c.IsTwo u ∧ IsS c.Le u e

/-- `e` numbers the code `pair e₁ e₂`. -/
def IsPairE (e e₁ e₂ : D) : Prop := ∃ p q, c.Pr e₁ e₂ p ∧ c.Quad p q ∧ c.Plus4 q e

/-- `e` numbers the code `prec e₁ e₂`. -/
def IsPrecE (e e₁ e₂ : D) : Prop := ∃ p q, c.Pr e₁ e₂ p ∧ c.Quad p q ∧ c.Plus5 q e

/-- `e` numbers the code `comp e₁ e₂`. -/
def IsCompE (e e₁ e₂ : D) : Prop := ∃ p q, c.Pr e₁ e₂ p ∧ c.Quad p q ∧ c.Plus6 q e

/-- `e` numbers the code `rfind' e₁`. -/
def IsRfindE (e e₁ : D) : Prop := ∃ q, c.Quad e₁ q ∧ c.Plus7 q e

/-- The successor rule of the pairing, on the segment: this is
`DescriptiveComplexity.CodeHalt.NextP` with the arithmetic replaced by the
guessed order. -/
def NextPR (a' b' a b : D) : Prop :=
  (c.Lt a' b' ∧ IsS c.Le a' a ∧ c.Lt a b' ∧ b = b') ∨
    (IsS c.Le a' b' ∧ a = b' ∧ IsZ c.Le b) ∨
      (c.Le b' a' ∧ IsS c.Le b' b ∧ c.Le b a' ∧ a = a') ∨
        (a' = b' ∧ IsZ c.Le a ∧ IsS c.Le b' b)

variable [Language.code.Structure A]

/-- **What justifies “the node `n` draws the code numbered `e`”**: the
constructor mark of `n`, and – for the four binary constructors – children
drawing the codes the number of `e` is built from. -/
def DecStep (n : A) (e : D) : Prop :=
  (CZero n ∧ IsZ c.Le e) ∨
    (CSucc n ∧ c.IsOne e) ∨
      (CLeft n ∧ c.IsTwo e) ∨
        (CRight n ∧ c.IsThree e) ∨
          (CPair n ∧ ∃ f g e₁ e₂, CArg1 n f ∧ CArg2 n g ∧ c.Dec f e₁ ∧ c.Dec g e₂ ∧
              c.IsPairE e e₁ e₂) ∨
            (CComp n ∧ ∃ f g e₁ e₂, CArg1 n f ∧ CArg2 n g ∧ c.Dec f e₁ ∧ c.Dec g e₂ ∧
                c.IsCompE e e₁ e₂) ∨
              (CPrec n ∧ ∃ f g e₁ e₂, CArg1 n f ∧ CArg2 n g ∧ c.Dec f e₁ ∧ c.Dec g e₂ ∧
                  c.IsPrecE e e₁ e₂) ∨
                (CRfind n ∧ ∃ f e₁, CArg1 n f ∧ c.Dec f e₁ ∧ c.IsRfindE e e₁)

/-- **What justifies “the code numbered `e` returns `v` on `x`”**: one clause
per constructor, mirroring `Nat.Partrec.Code.eval`. The `prec` clause is the
only one appealing to `e` itself, and it does so at a strictly smaller
argument; the `rfind'` clause states its search by a bounded universal. -/
def EvStep (e x v : D) : Prop :=
  (IsZ c.Le e ∧ IsZ c.Le v) ∨
    (c.IsOne e ∧ IsS c.Le x v) ∨
      (c.IsTwo e ∧ ∃ b, c.Pr v b x) ∨
        (c.IsThree e ∧ ∃ a, c.Pr a v x) ∨
          (∃ e₁ e₂, c.IsPairE e e₁ e₂ ∧ ∃ a b, c.Ev e₁ x a ∧ c.Ev e₂ x b ∧ c.Pr a b v) ∨
            (∃ e₁ e₂, c.IsCompE e e₁ e₂ ∧ ∃ y, c.Ev e₂ x y ∧ c.Ev e₁ y v) ∨
              (∃ e₁ e₂, c.IsPrecE e e₁ e₂ ∧
                  ((∃ a z, IsZ c.Le z ∧ c.Pr a z x ∧ c.Ev e₁ a v) ∨
                    ∃ a j j' x' i q r, IsS c.Le j' j ∧ c.Pr a j x ∧ c.Pr a j' x' ∧
                      c.Ev e x' i ∧ c.Pr j' i q ∧ c.Pr a q r ∧ c.Ev e₂ r v)) ∨
                (∃ e₁, c.IsRfindE e e₁ ∧ ∃ a b q₀ z, c.Pr a b x ∧ c.Le b v ∧ c.Pr a v q₀ ∧
                  IsZ c.Le z ∧ c.Ev e₁ q₀ z ∧
                  ∀ w, c.Le b w → c.Lt w v → ∃ q u, c.Pr a w q ∧ c.Ev e₁ q u ∧ ¬IsZ c.Le u)

end Cert

/-- **The conditions making the guessed relations a halting computation.** Four
justification rules and the root clause; the segment's order is linear, and
that is the only shape condition, all the rest being support. -/
structure CertOK {A D : Type} [Language.code.Structure A] (c : Cert A D) : Prop where
  /-- The numeral segment is linearly ordered. -/
  le_lin : IsLinOrd c.Le
  /-- Every addition fact is justified by the recurrence. -/
  add_ok : ∀ x y z, c.Add x y z →
    (IsZ c.Le y ∧ z = x) ∨ ∃ y' z', IsS c.Le y' y ∧ IsS c.Le z' z ∧ c.Add x y' z'
  /-- Every pairing fact is justified by the successor rule. -/
  pr_ok : ∀ a b p, c.Pr a b p →
    (IsZ c.Le p ∧ IsZ c.Le a ∧ IsZ c.Le b) ∨
      ∃ p' a' b', IsS c.Le p' p ∧ c.Pr a' b' p' ∧ c.NextPR a' b' a b
  /-- Every decoding fact is justified by the node's mark and its children. -/
  dec_ok : ∀ n e, c.Dec n e → c.DecStep n e
  /-- Every evaluation fact is justified by the rules of its code. -/
  ev_ok : ∀ e x v, c.Ev e x v → c.EvStep e x v
  /-- The root draws a code that returns something on `0`. -/
  root : ∃ (n : A) (e z v : D), CRoot n ∧ c.Dec n e ∧ IsZ c.Le z ∧ c.Ev e z v

/-! ### Soundness: a certificate really is a halting computation

Every guessed relation means what its name says, by induction along the two
things a justification decreases: the numeral of a code, and – inside the one
rule that keeps the code – the argument. -/

section Sound

variable {A D : Type} [Language.code.Structure A] [Finite D] {c : Cert A D} (h : CertOK c)
include h

theorem lt_sound {x y : D} : c.Lt x y ↔ numOf c.Le x < numOf c.Le y :=
  ⟨fun hxy => numOf_lt h.le_lin hxy.1 hxy.2, fun hxy => le_of_numOf_lt h.le_lin hxy⟩

theorem add_sound : ∀ (Y : ℕ) (x y z : D), numOf c.Le y = Y → c.Add x y z →
    numOf c.Le x + numOf c.Le y = numOf c.Le z := by
  intro Y
  induction Y using Nat.strong_induction_on with
  | _ Y ih =>
    rintro x y z rfl hadd
    rcases h.add_ok x y z hadd with ⟨hz, rfl⟩ | ⟨y', z', hy', hz', hadd'⟩
    · rw [(isZ_iff h.le_lin).mp hz]
      omega
    · have h1 := (isS_iff h.le_lin).mp hy'
      have h2 := (isS_iff h.le_lin).mp hz'
      have h3 := ih (numOf c.Le y') (by omega) x y' z' rfl hadd'
      omega

theorem nextPR_sound {a' b' a b : D} (hn : c.NextPR a' b' a b) :
    NextP (numOf c.Le a') (numOf c.Le b') (numOf c.Le a) (numOf c.Le b) := by
  rcases hn with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨(lt_sound h).mp h1, (isS_iff h.le_lin).mp h2, (lt_sound h).mp h3, by rw [h4]⟩
  · exact Or.inr (Or.inl ⟨(isS_iff h.le_lin).mp h1, by rw [h2], (isZ_iff h.le_lin).mp h3⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨(le_iff_numOf_le h.le_lin).mp h1, (isS_iff h.le_lin).mp h2,
      (le_iff_numOf_le h.le_lin).mp h3, by rw [h4]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by rw [h1], (isZ_iff h.le_lin).mp h2,
      (isS_iff h.le_lin).mp h3⟩))

theorem pr_sound : ∀ (P : ℕ) (a b p : D), numOf c.Le p = P → c.Pr a b p →
    Nat.pair (numOf c.Le a) (numOf c.Le b) = numOf c.Le p := by
  intro P
  induction P using Nat.strong_induction_on with
  | _ P ih =>
    rintro a b p rfl hpr
    rcases h.pr_ok a b p hpr with ⟨hp, ha, hb⟩ | ⟨p', a', b', hp', hpr', hnext⟩
    · rw [(isZ_iff h.le_lin).mp ha, (isZ_iff h.le_lin).mp hb, (isZ_iff h.le_lin).mp hp]
      simp [Nat.pair]
    · have h1 := (isS_iff h.le_lin).mp hp'
      have h2 := ih (numOf c.Le p') (by omega) a' b' p' rfl hpr'
      have h3 := pair_next (nextPR_sound h hnext)
      omega

theorem quad_sound {p q : D} (hq : c.Quad p q) : numOf c.Le q = 4 * numOf c.Le p := by
  obtain ⟨s, h1, h2⟩ := hq
  have e1 := add_sound h _ p p s rfl h1
  have e2 := add_sound h _ s s q rfl h2
  omega

theorem plus4_sound {q e : D} (he : c.Plus4 q e) : numOf c.Le e = numOf c.Le q + 4 := by
  obtain ⟨u₁, u₂, u₃, h1, h2, h3, h4⟩ := he
  have e1 := (isS_iff h.le_lin).mp h1
  have e2 := (isS_iff h.le_lin).mp h2
  have e3 := (isS_iff h.le_lin).mp h3
  have e4 := (isS_iff h.le_lin).mp h4
  omega

theorem plus5_sound {q e : D} (he : c.Plus5 q e) : numOf c.Le e = numOf c.Le q + 5 := by
  obtain ⟨u, h1, h2⟩ := he
  have e1 := plus4_sound h h1
  have e2 := (isS_iff h.le_lin).mp h2
  omega

theorem plus6_sound {q e : D} (he : c.Plus6 q e) : numOf c.Le e = numOf c.Le q + 6 := by
  obtain ⟨u, h1, h2⟩ := he
  have e1 := plus5_sound h h1
  have e2 := (isS_iff h.le_lin).mp h2
  omega

theorem plus7_sound {q e : D} (he : c.Plus7 q e) : numOf c.Le e = numOf c.Le q + 7 := by
  obtain ⟨u, h1, h2⟩ := he
  have e1 := plus6_sound h h1
  have e2 := (isS_iff h.le_lin).mp h2
  omega

theorem isOne_sound {e : D} (he : c.IsOne e) : numOf c.Le e = 1 := by
  obtain ⟨z, h1, h2⟩ := he
  have e1 := (isZ_iff h.le_lin).mp h1
  have e2 := (isS_iff h.le_lin).mp h2
  omega

theorem isTwo_sound {e : D} (he : c.IsTwo e) : numOf c.Le e = 2 := by
  obtain ⟨u, h1, h2⟩ := he
  have e1 := isOne_sound h h1
  have e2 := (isS_iff h.le_lin).mp h2
  omega

theorem isThree_sound {e : D} (he : c.IsThree e) : numOf c.Le e = 3 := by
  obtain ⟨u, h1, h2⟩ := he
  have e1 := isTwo_sound h h1
  have e2 := (isS_iff h.le_lin).mp h2
  omega

theorem isPairE_sound {e e₁ e₂ : D} (he : c.IsPairE e e₁ e₂) :
    numOf c.Le e = 4 * Nat.pair (numOf c.Le e₁) (numOf c.Le e₂) + 4 := by
  obtain ⟨p, q, h1, h2, h3⟩ := he
  have e1 := pr_sound h _ e₁ e₂ p rfl h1
  have e2 := quad_sound h h2
  have e3 := plus4_sound h h3
  omega

theorem isPrecE_sound {e e₁ e₂ : D} (he : c.IsPrecE e e₁ e₂) :
    numOf c.Le e = 4 * Nat.pair (numOf c.Le e₁) (numOf c.Le e₂) + 5 := by
  obtain ⟨p, q, h1, h2, h3⟩ := he
  have e1 := pr_sound h _ e₁ e₂ p rfl h1
  have e2 := quad_sound h h2
  have e3 := plus5_sound h h3
  omega

theorem isCompE_sound {e e₁ e₂ : D} (he : c.IsCompE e e₁ e₂) :
    numOf c.Le e = 4 * Nat.pair (numOf c.Le e₁) (numOf c.Le e₂) + 6 := by
  obtain ⟨p, q, h1, h2, h3⟩ := he
  have e1 := pr_sound h _ e₁ e₂ p rfl h1
  have e2 := quad_sound h h2
  have e3 := plus6_sound h h3
  omega

theorem isRfindE_sound {e e₁ : D} (he : c.IsRfindE e e₁) :
    numOf c.Le e = 4 * numOf c.Le e₁ + 7 := by
  obtain ⟨q, h1, h2⟩ := he
  have e1 := quad_sound h h1
  have e2 := plus7_sound h h2
  omega

/-- **The node really draws the code its number denotes.** -/
theorem dec_sound : ∀ (E : ℕ) (n : A) (e : D), numOf c.Le e = E → c.Dec n e →
    DecodesTo n (dec (numOf c.Le e)) := by
  intro E
  induction E using Nat.strong_induction_on with
  | _ E ih =>
    rintro n e rfl hdec
    rcases h.dec_ok n e hdec with ⟨hm, he⟩ | ⟨hm, he⟩ | ⟨hm, he⟩ | ⟨hm, he⟩ |
      ⟨hm, f, g, e₁, e₂, hf, hg, hdf, hdg, he⟩ | ⟨hm, f, g, e₁, e₂, hf, hg, hdf, hdg, he⟩ |
      ⟨hm, f, g, e₁, e₂, hf, hg, hdf, hdg, he⟩ | ⟨hm, f, e₁, hf, hdf, he⟩
    · rw [(isZ_iff h.le_lin).mp he, dec_zero]; exact hm
    · rw [isOne_sound h he, dec_one]; exact hm
    · rw [isTwo_sound h he, dec_two]; exact hm
    · rw [isThree_sound h he, dec_three]; exact hm
    · have hE := isPairE_sound h he
      obtain ⟨l1, l2⟩ := lt_of_pair_encode (numOf c.Le e₁) (numOf c.Le e₂)
      rw [hE, dec_pair]
      exact ⟨hm, f, g, hf, hg, ih (numOf c.Le e₁) (by omega) f e₁ rfl hdf,
        ih (numOf c.Le e₂) (by omega) g e₂ rfl hdg⟩
    · have hE := isCompE_sound h he
      obtain ⟨l1, l2⟩ := lt_of_pair_encode (numOf c.Le e₁) (numOf c.Le e₂)
      rw [hE, dec_comp]
      exact ⟨hm, f, g, hf, hg, ih (numOf c.Le e₁) (by omega) f e₁ rfl hdf,
        ih (numOf c.Le e₂) (by omega) g e₂ rfl hdg⟩
    · have hE := isPrecE_sound h he
      obtain ⟨l1, l2⟩ := lt_of_pair_encode (numOf c.Le e₁) (numOf c.Le e₂)
      rw [hE, dec_prec]
      exact ⟨hm, f, g, hf, hg, ih (numOf c.Le e₁) (by omega) f e₁ rfl hdf,
        ih (numOf c.Le e₂) (by omega) g e₂ rfl hdg⟩
    · have hE := isRfindE_sound h he
      rw [hE, dec_rfind]
      exact ⟨hm, f, hf, ih (numOf c.Le e₁) (by omega) f e₁ rfl hdf⟩

/-- **The code really returns what the certificate says.** The induction is on
the pair (number of the code, argument), lexicographically: every rule but the
recursive one of `prec` appeals to a strictly smaller code number, and that one
appeals to the same code at a strictly smaller argument. -/
theorem ev_sound : ∀ (E X : ℕ) (e x v : D), numOf c.Le e = E → numOf c.Le x = X →
    c.Ev e x v → numOf c.Le v ∈ eval (dec (numOf c.Le e)) (numOf c.Le x) := by
  intro E
  induction E using Nat.strong_induction_on with
  | _ E ihE =>
    intro X
    induction X using Nat.strong_induction_on with
    | _ X ihX =>
      rintro e x v rfl rfl hev
      rcases h.ev_ok e x v hev with ⟨he, hv⟩ | ⟨he, hs⟩ | ⟨he, b, hpr⟩ | ⟨he, a, hpr⟩ |
        ⟨e₁, e₂, hpe, a, b, hea, heb, hpr⟩ | ⟨e₁, e₂, hce, y, hey, hev₁⟩ |
        ⟨e₁, e₂, hpe, hcase⟩ | ⟨e₁, hre, a, b, q₀, z, hpx, hbv, hpq₀, hz, hev₀, hall⟩
      · rw [(isZ_iff h.le_lin).mp he, dec_zero, (isZ_iff h.le_lin).mp hv]
        exact mem_eval_zero
      · rw [isOne_sound h he, dec_one, (isS_iff h.le_lin).mp hs]
        exact mem_eval_succ
      · have hp := pr_sound h _ v b x rfl hpr
        rw [isTwo_sound h he, dec_two, ← hp]
        have hl := mem_eval_left (n := Nat.pair (numOf c.Le v) (numOf c.Le b))
        rwa [Nat.unpair_pair] at hl
      · have hp := pr_sound h _ a v x rfl hpr
        rw [isThree_sound h he, dec_three, ← hp]
        have hr := mem_eval_right (n := Nat.pair (numOf c.Le a) (numOf c.Le v))
        rwa [Nat.unpair_pair] at hr
      · have hE := isPairE_sound h hpe
        obtain ⟨l1, l2⟩ := lt_of_pair_encode (numOf c.Le e₁) (numOf c.Le e₂)
        have ha := ihE (numOf c.Le e₁) (by omega) (numOf c.Le x) e₁ x a rfl rfl hea
        have hb := ihE (numOf c.Le e₂) (by omega) (numOf c.Le x) e₂ x b rfl rfl heb
        have hpp := pr_sound h _ a b v rfl hpr
        rw [hE, dec_pair, ← hpp]
        exact mem_eval_pair ha hb
      · have hE := isCompE_sound h hce
        obtain ⟨l1, l2⟩ := lt_of_pair_encode (numOf c.Le e₁) (numOf c.Le e₂)
        have hy := ihE (numOf c.Le e₂) (by omega) (numOf c.Le x) e₂ x y rfl rfl hey
        have hvv := ihE (numOf c.Le e₁) (by omega) (numOf c.Le y) e₁ y v rfl rfl hev₁
        rw [hE, dec_comp]
        exact mem_eval_comp hy hvv
      · have hE := isPrecE_sound h hpe
        obtain ⟨l1, l2⟩ := lt_of_pair_encode (numOf c.Le e₁) (numOf c.Le e₂)
        rcases hcase with ⟨a, z, hz, hpr, hev₁⟩ |
          ⟨a, j, j', x', i, q, r, hjs, hpj, hpj', hevx, hpq, hpr₂, hev₂⟩
        · have hp := pr_sound h _ a z x rfl hpr
          rw [(isZ_iff h.le_lin).mp hz] at hp
          have hvv := ihE (numOf c.Le e₁) (by omega) (numOf c.Le a) e₁ a v rfl rfl hev₁
          rw [hE, dec_prec, ← hp]
          exact mem_eval_prec_zero hvv
        · have hj := (isS_iff h.le_lin).mp hjs
          have hpjv := pr_sound h _ a j x rfl hpj
          have hpj'v := pr_sound h _ a j' x' rfl hpj'
          have hqv := pr_sound h _ j' i q rfl hpq
          have hrv := pr_sound h _ a q r rfl hpr₂
          have hlt : numOf c.Le x' < numOf c.Le x := by
            rw [← hpjv, ← hpj'v, hj]
            exact Nat.pair_lt_pair_right _ (by omega)
          have hi := ihX (numOf c.Le x') hlt e x' i rfl rfl hevx
          have hvv := ihE (numOf c.Le e₂) (by omega) (numOf c.Le r) e₂ r v rfl rfl hev₂
          rw [hE, dec_prec] at hi
          rw [← hpj'v] at hi
          rw [← hrv, ← hqv] at hvv
          rw [hE, dec_prec, ← hpjv, hj]
          exact mem_eval_prec_succ hi hvv
      · have hE := isRfindE_sound h hre
        have hx := pr_sound h _ a b x rfl hpx
        have hq₀ := pr_sound h _ a v q₀ rfl hpq₀
        have h0 := ihE (numOf c.Le e₁) (by omega) (numOf c.Le q₀) e₁ q₀ z rfl rfl hev₀
        rw [(isZ_iff h.le_lin).mp hz, ← hq₀] at h0
        rw [hE, dec_rfind, ← hx]
        refine mem_eval_rfind' ((le_iff_numOf_le h.le_lin).mp hbv) h0 ?_
        intro w hw hwv
        obtain ⟨w', rfl⟩ := exists_numOf h.le_lin (numOf c.Le v) v rfl w (by omega)
        obtain ⟨q, u, hpq, heu, hu0⟩ :=
          hall w' ((le_iff_numOf_le h.le_lin).mpr hw) ((lt_sound h).mpr hwv)
        have hqq := pr_sound h _ a w' q rfl hpq
        have hue := ihE (numOf c.Le e₁) (by omega) (numOf c.Le q) e₁ q u rfl rfl heu
        refine ⟨numOf c.Le u, fun hzz => hu0 ((isZ_iff h.le_lin).mpr hzz), ?_⟩
        rwa [← hqq] at hue

/-- **A certificate exhibits a yes-instance.** -/
theorem holds_of_certOK : CODEHALT A := by
  obtain ⟨n, e, z, v, hroot, hdec, hz, hev⟩ := h.root
  refine ⟨n, dec (numOf c.Le e), hroot, dec_sound h _ n e rfl hdec, ?_⟩
  have hm := ev_sound h _ _ e z v rfl rfl hev
  rw [(isZ_iff h.le_lin).mp hz] at hm
  exact Part.dom_iff_mem.mpr ⟨_, hm⟩

end Sound

/-! ### Completeness: a halting computation is a certificate

The segment is `Fin (N + 1)`, with `N` large enough to hold the number of the
code, the step budget, and every value a bounded evaluation within that budget
can return (`DescriptiveComplexity.CodeHalt.valBound`). That is the only place
where finiteness of the certificate is at stake: every number the justification
rules appeal to is either an *argument* of a bounded evaluation, hence below the
budget, or one of its *values*, hence below the bound. -/

section Complete

variable {A : Type} [Language.code.Structure A]

/-- A number at most `N`, as a value of the segment. -/
def numVal {N : ℕ} (a : ℕ) (h : a ≤ N) : Fin (N + 1) := ⟨a, by omega⟩

@[simp]
theorem numVal_val {N a : ℕ} (h : a ≤ N) : ((numVal a h : Fin (N + 1)) : ℕ) = a := rfl

/-- **The certificate a halting bounded evaluation carries**: numerals up to
`N`, addition and pairing read off `ℕ`, the code each node draws, and the values
a bounded evaluation with budget `k` returns for codes numbered at most `E`. -/
def finCert (A : Type) [Language.code.Structure A] (E k N : ℕ) : Cert A (Fin (N + 1)) where
  Le i j := i ≤ j
  Add x y z := (x : ℕ) + (y : ℕ) = (z : ℕ)
  Pr a b p := Nat.pair (a : ℕ) (b : ℕ) = (p : ℕ)
  Dec n e := ∃ c', DecodesTo n c' ∧ encodeCode c' = (e : ℕ)
  Ev e x v := (e : ℕ) ≤ E ∧ (v : ℕ) ∈ evaln k (dec (e : ℕ)) (x : ℕ)

variable {E k N : ℕ}

@[simp] theorem finCert_add {x y z : Fin (N + 1)} :
    (finCert A E k N).Add x y z ↔ (x : ℕ) + (y : ℕ) = (z : ℕ) := Iff.rfl

@[simp] theorem finCert_pr {a b p : Fin (N + 1)} :
    (finCert A E k N).Pr a b p ↔ Nat.pair (a : ℕ) (b : ℕ) = (p : ℕ) := Iff.rfl

@[simp] theorem finCert_dec {n : A} {e : Fin (N + 1)} :
    (finCert A E k N).Dec n e ↔ ∃ c', DecodesTo n c' ∧ encodeCode c' = (e : ℕ) := Iff.rfl

@[simp] theorem finCert_ev {e x v : Fin (N + 1)} :
    (finCert A E k N).Ev e x v ↔
      (e : ℕ) ≤ E ∧ (v : ℕ) ∈ evaln k (dec (e : ℕ)) (x : ℕ) := Iff.rfl

@[simp] theorem finCert_isZ {i : Fin (N + 1)} :
    IsZ (finCert A E k N).Le i ↔ (i : ℕ) = 0 := isZ_fin

@[simp] theorem finCert_isS {i j : Fin (N + 1)} :
    IsS (finCert A E k N).Le i j ↔ (j : ℕ) = (i : ℕ) + 1 := isS_fin

@[simp] theorem finCert_le {i j : Fin (N + 1)} :
    (finCert A E k N).Le i j ↔ (i : ℕ) ≤ (j : ℕ) := Fin.le_def

@[simp] theorem finCert_lt {i j : Fin (N + 1)} :
    (finCert A E k N).Lt i j ↔ (i : ℕ) < (j : ℕ) := by
  constructor
  · rintro ⟨hle, hne⟩
    have : (i : ℕ) ≤ (j : ℕ) := hle
    exact lt_of_le_of_ne this fun hh => hne (Fin.ext hh)
  · intro hij
    exact ⟨show i ≤ j by rw [Fin.le_def]; omega, fun hh => by rw [hh] at hij; omega⟩

theorem finCert_quad {p q : Fin (N + 1)} (hq : (q : ℕ) = 4 * (p : ℕ)) :
    (finCert A E k N).Quad p q := by
  have hb := q.isLt
  exact ⟨numVal (2 * (p : ℕ)) (by omega), by simp; omega, by simp; omega⟩

theorem finCert_plus4 {q e : Fin (N + 1)} (he : (e : ℕ) = (q : ℕ) + 4) :
    (finCert A E k N).Plus4 q e := by
  have hb := e.isLt
  exact ⟨numVal ((q : ℕ) + 1) (by omega), numVal ((q : ℕ) + 2) (by omega),
    numVal ((q : ℕ) + 3) (by omega), by simp, by simp, by simp, by simp; omega⟩

theorem finCert_plus5 {q e : Fin (N + 1)} (he : (e : ℕ) = (q : ℕ) + 5) :
    (finCert A E k N).Plus5 q e := by
  have hb := e.isLt
  exact ⟨numVal ((q : ℕ) + 4) (by omega), finCert_plus4 (by simp), by simp; omega⟩

theorem finCert_plus6 {q e : Fin (N + 1)} (he : (e : ℕ) = (q : ℕ) + 6) :
    (finCert A E k N).Plus6 q e := by
  have hb := e.isLt
  exact ⟨numVal ((q : ℕ) + 5) (by omega), finCert_plus5 (by simp), by simp; omega⟩

theorem finCert_plus7 {q e : Fin (N + 1)} (he : (e : ℕ) = (q : ℕ) + 7) :
    (finCert A E k N).Plus7 q e := by
  have hb := e.isLt
  exact ⟨numVal ((q : ℕ) + 6) (by omega), finCert_plus6 (by simp), by simp; omega⟩

theorem finCert_isOne {e : Fin (N + 1)} (he : (e : ℕ) = 1) : (finCert A E k N).IsOne e :=
  ⟨numVal 0 (Nat.zero_le _), by simp, by simp [he]⟩

theorem finCert_isTwo {e : Fin (N + 1)} (he : (e : ℕ) = 2) : (finCert A E k N).IsTwo e := by
  have hb := e.isLt
  exact ⟨numVal 1 (by omega), finCert_isOne rfl, by simp [he]⟩

theorem finCert_isThree {e : Fin (N + 1)} (he : (e : ℕ) = 3) : (finCert A E k N).IsThree e := by
  have hb := e.isLt
  exact ⟨numVal 2 (by omega), finCert_isTwo rfl, by simp [he]⟩

theorem finCert_isPairE {e e₁ e₂ : Fin (N + 1)}
    (he : (e : ℕ) = 4 * Nat.pair (e₁ : ℕ) (e₂ : ℕ) + 4) : (finCert A E k N).IsPairE e e₁ e₂ := by
  have hb := e.isLt
  exact ⟨numVal (Nat.pair (e₁ : ℕ) (e₂ : ℕ)) (by omega),
    numVal (4 * Nat.pair (e₁ : ℕ) (e₂ : ℕ)) (by omega), rfl, finCert_quad (by simp),
    finCert_plus4 (by simp; omega)⟩

theorem finCert_isPrecE {e e₁ e₂ : Fin (N + 1)}
    (he : (e : ℕ) = 4 * Nat.pair (e₁ : ℕ) (e₂ : ℕ) + 5) : (finCert A E k N).IsPrecE e e₁ e₂ := by
  have hb := e.isLt
  exact ⟨numVal (Nat.pair (e₁ : ℕ) (e₂ : ℕ)) (by omega),
    numVal (4 * Nat.pair (e₁ : ℕ) (e₂ : ℕ)) (by omega), rfl, finCert_quad (by simp),
    finCert_plus5 (by simp; omega)⟩

theorem finCert_isCompE {e e₁ e₂ : Fin (N + 1)}
    (he : (e : ℕ) = 4 * Nat.pair (e₁ : ℕ) (e₂ : ℕ) + 6) : (finCert A E k N).IsCompE e e₁ e₂ := by
  have hb := e.isLt
  exact ⟨numVal (Nat.pair (e₁ : ℕ) (e₂ : ℕ)) (by omega),
    numVal (4 * Nat.pair (e₁ : ℕ) (e₂ : ℕ)) (by omega), rfl, finCert_quad (by simp),
    finCert_plus6 (by simp; omega)⟩

theorem finCert_isRfindE {e e₁ : Fin (N + 1)} (he : (e : ℕ) = 4 * (e₁ : ℕ) + 7) :
    (finCert A E k N).IsRfindE e e₁ := by
  have hb := e.isLt
  exact ⟨numVal (4 * (e₁ : ℕ)) (by omega), finCert_quad (by simp), finCert_plus7 (by simp; omega)⟩

theorem finCert_nextPR {a' b' a b : Fin (N + 1)}
    (h : NextP (a' : ℕ) (b' : ℕ) (a : ℕ) (b : ℕ)) : (finCert A E k N).NextPR a' b' a b := by
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨by simp [h1], by simp [h2], by simp [h3], Fin.ext h4⟩
  · exact Or.inr (Or.inl ⟨by simp [h1], Fin.ext h2, by simp [h3]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by simp [h1], by simp [h2], by simp [h3], Fin.ext h4⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨Fin.ext h1, by simp [h2], by simp [h3]⟩))

/-- **A halting computation is a certificate.** -/
theorem certOK_finCert (hEN : E ≤ N) (hkN : k ≤ N) (hbN : valBound E k ≤ N)
    {n₀ : A} {c₀ : Nat.Partrec.Code} {v₀ : ℕ} (hroot : CRoot n₀) (hdec : DecodesTo n₀ c₀)
    (hE : encodeCode c₀ = E) (hv : v₀ ∈ evaln k c₀ 0) : CertOK (finCert A E k N) := by
  obtain _ | k := k
  · simp [evaln] at hv
  have hdecE : dec E = c₀ := by rw [← hE, dec_encodeCode]
  refine ⟨isLinOrd_le, ?_, ?_, ?_, ?_, ?_⟩
  · -- addition
    intro x y z hxyz
    have hxb := x.isLt
    have hyb := y.isLt
    have hzb := z.isLt
    have hxyz' : (x : ℕ) + (y : ℕ) = (z : ℕ) := hxyz
    rcases Nat.eq_zero_or_pos (y : ℕ) with hy | hy
    · exact Or.inl ⟨by simp [hy], Fin.ext (by omega)⟩
    · exact Or.inr ⟨numVal ((y : ℕ) - 1) (by omega), numVal ((z : ℕ) - 1) (by omega),
        by simp; omega, by simp; omega, by simp; omega⟩
  · -- pairing
    intro a b p hp
    have hpb := p.isLt
    have hp' : Nat.pair (a : ℕ) (b : ℕ) = (p : ℕ) := hp
    rcases Nat.eq_zero_or_pos (p : ℕ) with h0 | h0
    · obtain ⟨ha, hb⟩ := pair_eq_zero (show Nat.pair (a : ℕ) (b : ℕ) = 0 by omega)
      exact Or.inl ⟨by simp [h0], by simp [ha], by simp [hb]⟩
    · obtain ⟨a', b', hstep, hnext⟩ :=
        exists_pred_pair (show Nat.pair (a : ℕ) (b : ℕ) ≠ 0 by omega)
      have hab : Nat.pair a' b' ≤ N := by omega
      refine Or.inr ⟨numVal (Nat.pair a' b') hab,
        numVal a' (le_trans (Nat.left_le_pair a' b') hab),
        numVal b' (le_trans (Nat.right_le_pair a' b') hab), by simp; omega, rfl, ?_⟩
      exact finCert_nextPR (by simpa using hnext)
  · -- decoding
    rintro n e ⟨c', hdec', hce⟩
    have heb := e.isLt
    cases c' with
    | zero => exact Or.inl ⟨hdec', by simp [← hce, encodeCode]⟩
    | succ => exact Or.inr (Or.inl ⟨hdec', finCert_isOne (by simp [← hce, encodeCode])⟩)
    | left => exact Or.inr (Or.inr (Or.inl ⟨hdec', finCert_isTwo (by simp [← hce, encodeCode])⟩))
    | right =>
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hdec', finCert_isThree
        (by simp [← hce, encodeCode])⟩)))
    | pair cf cg =>
      obtain ⟨hm, f, g, hf, hg, hf', hg'⟩ := hdec'
      have hEq : (e : ℕ) = 4 * Nat.pair (encodeCode cf) (encodeCode cg) + 4 := by
        rw [← hce, encodeCode_pair]
      obtain ⟨l1, l2⟩ := lt_of_pair_encode (encodeCode cf) (encodeCode cg)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, f, g,
        numVal (encodeCode cf) (by omega), numVal (encodeCode cg) (by omega), hf, hg,
        ⟨cf, hf', rfl⟩, ⟨cg, hg', rfl⟩, finCert_isPairE (by simpa using hEq)⟩))))
    | comp cf cg =>
      obtain ⟨hm, f, g, hf, hg, hf', hg'⟩ := hdec'
      have hEq : (e : ℕ) = 4 * Nat.pair (encodeCode cf) (encodeCode cg) + 6 := by
        rw [← hce, encodeCode_comp]
      obtain ⟨l1, l2⟩ := lt_of_pair_encode (encodeCode cf) (encodeCode cg)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, f, g,
        numVal (encodeCode cf) (by omega), numVal (encodeCode cg) (by omega), hf, hg,
        ⟨cf, hf', rfl⟩, ⟨cg, hg', rfl⟩, finCert_isCompE (by simpa using hEq)⟩)))))
    | prec cf cg =>
      obtain ⟨hm, f, g, hf, hg, hf', hg'⟩ := hdec'
      have hEq : (e : ℕ) = 4 * Nat.pair (encodeCode cf) (encodeCode cg) + 5 := by
        rw [← hce, encodeCode_prec]
      obtain ⟨l1, l2⟩ := lt_of_pair_encode (encodeCode cf) (encodeCode cg)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, f, g,
        numVal (encodeCode cf) (by omega), numVal (encodeCode cg) (by omega), hf, hg,
        ⟨cf, hf', rfl⟩, ⟨cg, hg', rfl⟩, finCert_isPrecE (by simpa using hEq)⟩))))))
    | rfind' cf =>
      obtain ⟨hm, f, hf, hf'⟩ := hdec'
      have hEq : (e : ℕ) = 4 * encodeCode cf + 7 := by rw [← hce, encodeCode_rfind']
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hm, f,
        numVal (encodeCode cf) (by omega), hf, ⟨cf, hf', rfl⟩,
        finCert_isRfindE (by simpa using hEq)⟩))))))
  · -- evaluation
    rintro e x v ⟨heE, hev⟩
    have heb := e.isLt
    have hxb := x.isLt
    have hvb := v.isLt
    obtain ⟨C, hCd⟩ : ∃ C, dec (e : ℕ) = C := ⟨_, rfl⟩
    have hCe : encodeCode C = (e : ℕ) := by rw [← hCd]; exact encodeCode_dec _
    rw [hCd] at hev
    cases C with
    | zero =>
      obtain ⟨-, hv0⟩ := mem_evaln_zero_iff.mp hev
      exact Or.inl ⟨by simp [← hCe, encodeCode], by simp [hv0]⟩
    | succ =>
      obtain ⟨-, hv1⟩ := mem_evaln_succ_iff.mp hev
      exact Or.inr (Or.inl ⟨finCert_isOne (by simp [← hCe, encodeCode]), by simp [hv1]⟩)
    | left =>
      obtain ⟨-, hvl⟩ := mem_evaln_left_iff.mp hev
      refine Or.inr (Or.inr (Or.inl ⟨finCert_isTwo (by simp [← hCe, encodeCode]),
        numVal (Nat.unpair (x : ℕ)).2 (le_trans (Nat.unpair_right_le _) (by omega)), ?_⟩))
      simp only [finCert_pr, numVal_val, hvl]
      exact Nat.pair_unpair _
    | right =>
      obtain ⟨-, hvr⟩ := mem_evaln_right_iff.mp hev
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨finCert_isThree (by simp [← hCe, encodeCode]),
        numVal (Nat.unpair (x : ℕ)).1 (le_trans (Nat.unpair_left_le _) (by omega)), ?_⟩)))
      simp only [finCert_pr, numVal_val, hvr]
      exact Nat.pair_unpair _
    | pair cf cg =>
      obtain ⟨-, a, b, ha, hb, hab⟩ := mem_evaln_pair_iff.mp hev
      have hEq : (e : ℕ) = 4 * Nat.pair (encodeCode cf) (encodeCode cg) + 4 := by
        rw [← hCe, encodeCode_pair]
      obtain ⟨l1, l2⟩ := lt_of_pair_encode (encodeCode cf) (encodeCode cg)
      have hla := Nat.left_le_pair a b
      have hlb := Nat.right_le_pair a b
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨numVal (encodeCode cf) (by omega), numVal (encodeCode cg) (by omega),
          finCert_isPairE (by simpa using hEq), numVal a (by omega), numVal b (by omega),
          ⟨by simp only [numVal_val]; omega, ?_⟩, ⟨by simp only [numVal_val]; omega, ?_⟩,
          by simp; omega⟩))))
      · simpa using ha
      · simpa using hb
    | comp cf cg =>
      obtain ⟨-, y, hy, hyv⟩ := mem_evaln_comp_iff.mp hev
      have hEq : (e : ℕ) = 4 * Nat.pair (encodeCode cf) (encodeCode cg) + 6 := by
        rw [← hCe, encodeCode_comp]
      obtain ⟨l1, l2⟩ := lt_of_pair_encode (encodeCode cf) (encodeCode cg)
      have hyk : y < k + 1 := evaln_bound hyv
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨numVal (encodeCode cf) (by omega), numVal (encodeCode cg) (by omega),
          finCert_isCompE (by simpa using hEq), numVal y (by omega),
          ⟨by simp only [numVal_val]; omega, ?_⟩, ⟨by simp only [numVal_val]; omega, ?_⟩⟩)))))
      · simpa using hy
      · simpa using hyv
    | prec cf cg =>
      have hEq : (e : ℕ) = 4 * Nat.pair (encodeCode cf) (encodeCode cg) + 5 := by
        rw [← hCe, encodeCode_prec]
      obtain ⟨l1, l2⟩ := lt_of_pair_encode (encodeCode cf) (encodeCode cg)
      rw [← Nat.pair_unpair (x : ℕ)] at hev
      have hax : (Nat.unpair (x : ℕ)).1 ≤ (x : ℕ) := Nat.unpair_left_le _
      have hmx : (Nat.unpair (x : ℕ)).2 ≤ (x : ℕ) := Nat.unpair_right_le _
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨numVal (encodeCode cf) (by omega), numVal (encodeCode cg) (by omega),
          finCert_isPrecE (by simpa using hEq), ?_⟩))))))
      rcases hm : (Nat.unpair (x : ℕ)).2 with _ | j
      · rw [hm] at hev
        obtain ⟨-, hcf⟩ := mem_evaln_prec_zero_iff.mp hev
        refine Or.inl ⟨numVal (Nat.unpair (x : ℕ)).1 (by omega), numVal 0 (Nat.zero_le _),
          by simp, ?_, ⟨by simp only [numVal_val]; omega, by simpa using hcf⟩⟩
        simp only [finCert_pr, numVal_val]
        conv_rhs => rw [← Nat.pair_unpair (x : ℕ)]
        rw [hm]
      · rw [hm] at hev
        obtain ⟨-, i, hi, hcg⟩ := mem_evaln_prec_succ_iff.mp hev
        have hik : Nat.pair (Nat.unpair (x : ℕ)).1 j < k := evaln_bound hi
        have hck : Nat.pair (Nat.unpair (x : ℕ)).1 (Nat.pair j i) < k + 1 := evaln_bound hcg
        have hji : Nat.pair j i ≤ Nat.pair (Nat.unpair (x : ℕ)).1 (Nat.pair j i) :=
          Nat.right_le_pair _ _
        have hii : i ≤ Nat.pair j i := Nat.right_le_pair _ _
        refine Or.inr ⟨numVal (Nat.unpair (x : ℕ)).1 (by omega),
          numVal ((Nat.unpair (x : ℕ)).2) (by omega), numVal j (by omega),
          numVal (Nat.pair (Nat.unpair (x : ℕ)).1 j) (by omega), numVal i (by omega),
          numVal (Nat.pair j i) (by omega),
          numVal (Nat.pair (Nat.unpair (x : ℕ)).1 (Nat.pair j i)) (by omega),
          by simp [hm], ?_, rfl, ⟨heE, ?_⟩, rfl, rfl, ⟨by simp only [numVal_val]; omega, ?_⟩⟩
        · simp only [finCert_pr, numVal_val]
          conv_rhs => rw [← Nat.pair_unpair (x : ℕ)]
        · rw [hCd]
          exact evaln_mono (Nat.le_succ _) hi
        · simpa using hcg
    | rfind' cf =>
      have hEq : (e : ℕ) = 4 * encodeCode cf + 7 := by rw [← hCe, encodeCode_rfind']
      rw [← Nat.pair_unpair (x : ℕ)] at hev
      have hax : (Nat.unpair (x : ℕ)).1 ≤ (x : ℕ) := Nat.unpair_left_le _
      have hmx : (Nat.unpair (x : ℕ)).2 ≤ (x : ℕ) := Nat.unpair_right_le _
      obtain ⟨hbv, h0, hall⟩ := evaln_rfind'_spec (k + 1) hev
      have h0k : Nat.pair (Nat.unpair (x : ℕ)).1 (v : ℕ) < k + 1 := evaln_bound h0
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨numVal (encodeCode cf) (by omega), finCert_isRfindE (by simpa using hEq),
          numVal (Nat.unpair (x : ℕ)).1 (by omega), numVal (Nat.unpair (x : ℕ)).2 (by omega),
          numVal (Nat.pair (Nat.unpair (x : ℕ)).1 (v : ℕ)) (by omega), numVal 0 (Nat.zero_le _),
          ?_, by simp; omega, rfl, by simp, ⟨by simp only [numVal_val]; omega, ?_⟩, ?_⟩))))))
      · simp only [finCert_pr, numVal_val]
        exact Nat.pair_unpair _
      · simpa using h0
      · intro w hw hwv
        simp only [finCert_le, numVal_val] at hw
        simp only [finCert_lt] at hwv
        obtain ⟨u, hu0, hu⟩ := hall (w : ℕ) hw hwv
        have hqk : Nat.pair (Nat.unpair (x : ℕ)).1 (w : ℕ) < k + 1 := evaln_bound hu
        have huN : u ≤ N :=
          le_trans (le_valBound (E := E) (e := encodeCode cf) (by omega)
            (by rw [dec_encodeCode]; exact hu)) hbN
        refine ⟨numVal (Nat.pair (Nat.unpair (x : ℕ)).1 (w : ℕ)) (by omega), numVal u huN,
          rfl, ⟨by simp only [numVal_val]; omega, ?_⟩, ?_⟩
        · simpa using hu
        · simp [hu0]
  · -- the root
    have hv0 : v₀ ≤ N :=
      le_trans (le_valBound (E := E) le_rfl (by rw [hdecE]; exact hv)) hbN
    exact ⟨n₀, numVal E hEN, numVal 0 (Nat.zero_le _), numVal v₀ hv0, hroot, ⟨c₀, hdec, hE⟩,
      by simp, ⟨le_rfl, by simp only [numVal_val, hdecE]; exact hv⟩⟩

end Complete

/-- **A yes-instance of `CODEHALT` is exactly one whose invented values carry a
certificate.** This is the mathematical content of `CODEHALT ∈ RE`; the syntax
is in `DescriptiveComplexity.Problems.CodeHalt.Membership`. -/
theorem codehalt_iff_cert (A : Type) [Language.code.Structure A] :
    CODEHALT A ↔ ∃ (m : ℕ) (c : Cert A (Fin m)), CertOK c := by
  constructor
  · rintro ⟨n₀, c₀, hroot, hdec, hdom⟩
    obtain ⟨v₀, hv₀⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨k, hk⟩ := evaln_complete.mp hv₀
    refine ⟨max (max (encodeCode c₀) k) (valBound (encodeCode c₀) k) + 1,
      finCert A (encodeCode c₀) k (max (max (encodeCode c₀) k) (valBound (encodeCode c₀) k)),
      certOK_finCert (by omega) (by omega) (by omega) hroot hdec rfl hk⟩
  · rintro ⟨m, c, hc⟩
    exact holds_of_certOK hc

end CodeHalt

end DescriptiveComplexity
