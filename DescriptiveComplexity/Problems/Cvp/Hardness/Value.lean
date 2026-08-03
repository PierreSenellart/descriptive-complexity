/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Cvp.Hardness.Wiring

/-!
# What the drawn circuit computes

The intended value of each gate of
`DescriptiveComplexity.Problems.Cvp.Hardness.Interp`, and the two halves of the
statement that the circuit computes it.

The **building** half (this file's first section) walks the chains: each gate's
value follows from its inputs', by induction along the order for the two chains
and by strong induction on the rank of the stage for the propagation, whose
gates at stage `s` read the propagation gates one stage below. The **inverting**
half is the converse, and it is one induction on the derivation
`DescriptiveComplexity.GateVal`: whatever the circuit derives, it derives for
the intended reason, because the wiring lemmas leave a gate no other input to
have derived it from.

Only the true rail carries information; the false rail is where the constant
`0` and the unfired chains sit, and nothing downstream reads it, so the
inverting half states nothing about it.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc CvpDraw

namespace CvpVal

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-! ### The intended values -/

/-- The value of a conjunction-chain gate: every negative literal of `c` up to
`y` is forced within `orank s` rounds. -/
def BdVal (c y s : A) : Prop := ∀ y' ≤ y, NegIn c y' → ForcedIn (orank s) y'

/-- The value of a propagation-chain gate: some clause up to `c` forces `x` in
one round from the stage `orank s`. -/
def HdVal (x c s : A) : Prop :=
  ∃ c' ≤ c, IsCl c' ∧ PosIn c' x ∧ ∀ y : A, NegIn c' y → ForcedIn (orank s) y

/-- The value of a top-stage conjunction-chain gate: every negative literal of
`c` up to `y` is forced at all. -/
def BdTopVal (c y : A) : Prop := ∀ y' ≤ y, NegIn c y' → Forced y'

/-- The value of a goal-chain gate: the instance is not Horn, or some clause up
to `c` is a goal clause whose negative literals are all forced. -/
def GlVal (c : A) : Prop :=
  ¬AtMostOnePositive A ∨
    ∃ c' ≤ c, IsCl c' ∧ (∀ x : A, ¬PosIn c' x) ∧ ∀ y : A, NegIn c' y → Forced y

/-! ### Reading the values off the stages -/

omit [Finite A] [Nonempty A] in
/-- At the top of the clause walk, a propagation gate is one round of unit
propagation. -/
theorem hdVal_top {M : A} (hM : ∀ a : A, a ≤ M) (x s : A) :
    HdVal x M s ↔ ForcedIn (orank s + 1) x := by
  constructor
  · rintro ⟨c, -, hc, hp, hneg⟩
    exact ⟨c, hc, hp, hneg⟩
  · rintro ⟨c, hc, hp, hneg⟩
    exact ⟨c, hM c, hc, hp, hneg⟩

omit [Finite A] [Nonempty A] in
/-- At the top of the literal walk, a conjunction gate is the body condition. -/
theorem bdVal_top {M : A} (hM : ∀ a : A, a ≤ M) (c s : A) :
    BdVal c M s ↔ ∀ y : A, NegIn c y → ForcedIn (orank s) y :=
  ⟨fun h y => h y (hM y), fun h y' _ => h y'⟩

/-- The last stage is the fixed point: `Nat.card A` rounds of propagation force
everything that is forced at all. -/
theorem forced_iff_top {M : A} (hM : ∀ a : A, a ≤ M) (x : A) :
    Forced x ↔ ForcedIn (orank M + 1) x := by
  have hcard : orank M + 1 = Nat.card A := by
    rw [orank_isTop hM]
    have : 0 < Nat.card A := Nat.card_pos
    omega
  rw [hcard]
  exact ⟨forced_forcedIn_card, fun h => ⟨_, h⟩⟩

/-! ### Building a derivation

Each gate evaluates to `1` as soon as its intended value holds. -/

section Build

variable {m M : A}

omit [Finite A] [Nonempty A] in
/-- The constant `1` gate derives `1`. -/
theorem gateVal_tt (hm : ∀ a : A, m ≤ a) : GateVal true (ttPt (A := A) m) :=
  .constTrue ((isTrue_iff .tt _).mpr ⟨rfl, fun a => hm a, fun a => hm a, fun a => hm a⟩)

omit [Nonempty A] in
/-- **The two chains of one stage**, by strong induction on the rank of the
stage: the conjunction chains of a stage read the propagation gates of the
stage below, and the propagation chain of a stage reads the conjunction chains
of its own. -/
theorem gateVal_stage (hm : ∀ a : A, m ≤ a) (hM : ∀ a : A, a ≤ M) :
    ∀ n : ℕ, ∀ s : A, orank s = n →
      (∀ c y : A, BdVal c y s → GateVal true (bdPt c y s)) ∧
        ∀ x c : A, HdVal x c s → GateVal true (hdPt x c s) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    -- The right input of a conjunction gate, at the literal `y` of the clause `c`.
    have hright : ∀ c y : A, (NegIn c y → ForcedIn (orank s) y) →
        ∃ q, RelMap (M := cvpInterp.Map A) circRight ![bdPt c y s, q] ∧ GateVal true q := by
      intro c y hy
      by_cases hneg : NegIn c y
      · -- the literal is negative in the clause: read the stage below
        have hforced := hy hneg
        by_cases hsmin : ∀ a : A, s ≤ a
        · rw [orank_eq_zero hsmin] at hforced
          exact hforced.elim
        · obtain ⟨s', hlt, hnb⟩ := exists_succ_of_not_min hsmin
          have hcov : s' ⋖ s := ⟨hlt, fun z hz hz' => hnb z ⟨hz, hz'⟩⟩
          have hrank : orank s = orank s' + 1 := orank_covBy hcov
          have hlt' : orank s' < n := by omega
          rw [hrank] at hforced
          have hhd : HdVal y M s' := (hdVal_top hM y s').mpr hforced
          refine ⟨hdPt y M s',
            (right_bd hm hM ![c, y, s] _).mpr (Or.inr (Or.inr ⟨hneg, s', hcov, rfl⟩)),
            (ih (orank s') hlt' s' rfl).2 y M hhd⟩
      · exact ⟨ttPt m, (right_bd hm hM ![c, y, s] _).mpr (Or.inl ⟨hneg, rfl⟩), gateVal_tt hm⟩
    -- the conjunction chains of this stage
    have hbd : ∀ c y : A, BdVal c y s → GateVal true (bdPt c y s) := by
      intro c y
      induction y using order_induction with
      | hmin y hy =>
        intro hval
        obtain ⟨q, hq, hqv⟩ := hright c y fun hneg => hval y le_rfl hneg
        exact .andTrue ((isAnd_iff .bd _).mpr (Or.inl rfl))
          ((left_bd hm ![c, y, s] _).mpr (Or.inl ⟨hy, rfl⟩)) hq (gateVal_tt hm) hqv
      | hstep y' y hlt hnb ihy =>
        intro hval
        have hcov : y' ⋖ y := ⟨hlt, fun z hz hz' => hnb z ⟨hz, hz'⟩⟩
        obtain ⟨q, hq, hqv⟩ := hright c y fun hneg => hval y le_rfl hneg
        exact .andTrue ((isAnd_iff .bd _).mpr (Or.inl rfl))
          ((left_bd hm ![c, y, s] _).mpr (Or.inr ⟨y', hcov, rfl⟩)) hq
          (ihy fun y'' hy'' hneg => hval y'' (hy''.trans hlt.le) hneg) hqv
    refine ⟨hbd, ?_⟩
    -- the propagation chain of this stage
    intro x c
    induction c using order_induction with
    | hmin c hc =>
      rintro ⟨c', hc', hcl, hp, hneg⟩
      have hcc : c' = c := le_antisymm hc' (hc c')
      subst hcc
      refine .orTrueRight ((isOr_iff .hd _).mpr (Or.inl rfl))
        ((right_hd hm hM ![x, c', s] _).mpr (Or.inl ⟨⟨hcl, hp⟩, rfl⟩)) ?_
      exact hbd c' M ((bdVal_top hM c' s).mpr hneg)
    | hstep c' c hlt hnb ihc =>
      rintro ⟨c'', hc'', hcl, hp, hneg⟩
      have hcov : c' ⋖ c := ⟨hlt, fun z hz hz' => hnb z ⟨hz, hz'⟩⟩
      rcases covBy_le_cases hcov hc'' with hle | rfl
      · exact .orTrueLeft ((isOr_iff .hd _).mpr (Or.inl rfl))
          ((left_hd hm ![x, c, s] _).mpr (Or.inr ⟨c', hcov, rfl⟩))
          (ihc ⟨c'', hle, hcl, hp, hneg⟩)
      · refine .orTrueRight ((isOr_iff .hd _).mpr (Or.inl rfl))
          ((right_hd hm hM ![x, c'', s] _).mpr (Or.inl ⟨⟨hcl, hp⟩, rfl⟩)) ?_
        exact hbd c'' M ((bdVal_top hM c'' s).mpr hneg)

/-- A conjunction gate of the top stage evaluates to `1` when its value
holds. -/
theorem gateVal_bdTop (hm : ∀ a : A, m ≤ a) (hM : ∀ a : A, a ≤ M) (c y : A)
    (hval : BdTopVal c y) : GateVal true (bdTopPt m c y) := by
  have hand : ∀ y : A, RelMap (M := cvpInterp.Map A) circIsAnd ![bdTopPt m c y] :=
    fun _ => (isAnd_iff .bdTop _).mpr (Or.inr ⟨rfl, fun a => hm a⟩)
  have hleft := fun y : A => left_bdTop hm ![c, y, m]
  have hright' := fun y : A => right_bdTop hm hM ![c, y, m]
  have hright : ∀ y : A, (NegIn c y → Forced y) →
      ∃ q, RelMap (M := cvpInterp.Map A) circRight ![bdTopPt m c y, q] ∧ GateVal true q := by
    intro y hy
    by_cases hneg : NegIn c y
    · refine ⟨hdPt y M M, (hright' y _ fun a => hm a).mpr (Or.inr ⟨hneg, rfl⟩), ?_⟩
      exact (gateVal_stage hm hM (orank M) M rfl).2 y M
        ((hdVal_top hM y M).mpr ((forced_iff_top hM y).mp (hy hneg)))
    · exact ⟨ttPt m, (hright' y _ fun a => hm a).mpr (Or.inl ⟨hneg, rfl⟩), gateVal_tt hm⟩
  induction y using order_induction with
  | hmin y hy =>
    obtain ⟨q, hq, hqv⟩ := hright y fun hneg => hval y le_rfl hneg
    exact .andTrue (hand y) ((hleft y _).mpr (Or.inl ⟨fun a => hm a, hy, rfl⟩)) hq
      (gateVal_tt hm) hqv
  | hstep y' y hlt hnb ihy =>
    have hcov : y' ⋖ y := ⟨hlt, fun z hz hz' => hnb z ⟨hz, hz'⟩⟩
    obtain ⟨q, hq, hqv⟩ := hright y fun hneg => hval y le_rfl hneg
    exact .andTrue (hand y) ((hleft y _).mpr (Or.inr ⟨fun a => hm a, y', hcov, rfl⟩)) hq
      (ihy fun y'' hy'' hneg => hval y'' (hy''.trans hlt.le) hneg) hqv

/-- A goal-chain gate evaluates to `1` when its value holds. -/
theorem gateVal_gl (hm : ∀ a : A, m ≤ a) (hM : ∀ a : A, a ≤ M) (c : A) (hval : GlVal c) :
    GateVal true (glPt m c) := by
  have hor : ∀ c : A, RelMap (M := cvpInterp.Map A) circIsOr ![glPt m c] :=
    fun _ => (isOr_iff .gl _).mpr (Or.inr ⟨rfl, fun a => hm a, fun a => hm a⟩)
  have hleft := fun c : A => fun q => left_gl hm ![c, m, m] q (fun a => hm a) fun a => hm a
  have hright := fun c : A => fun q => right_gl hm hM ![c, m, m] q (fun a => hm a) fun a => hm a
  -- the right input fires exactly at a goal clause whose body is forced
  have hgoal : ∀ c : A, IsCl c → (∀ x : A, ¬PosIn c x) → (∀ y : A, NegIn c y → Forced y) →
      GateVal true (glPt m c) := by
    intro c hcl hnp hneg
    exact .orTrueRight (hor c) ((hright c _).mpr (Or.inl ⟨⟨hcl, hnp⟩, rfl⟩))
      (gateVal_bdTop hm hM c M fun y' _ hn => hneg y' hn)
  induction c using order_induction with
  | hmin c hc =>
    rcases hval with hhorn | ⟨c', hc', hcl, hnp, hneg⟩
    · exact .orTrueLeft (hor c) ((hleft c _).mpr (Or.inr (Or.inl ⟨hc, hhorn, rfl⟩)))
        (gateVal_tt hm)
    · have hcc : c' = c := le_antisymm hc' (hc c')
      subst hcc
      exact hgoal c' hcl hnp hneg
  | hstep c' c hlt hnb ihc =>
    have hcov : c' ⋖ c := ⟨hlt, fun z hz hz' => hnb z ⟨hz, hz'⟩⟩
    rcases hval with hhorn | ⟨c'', hc'', hcl, hnp, hneg⟩
    · exact .orTrueLeft (hor c) ((hleft c _).mpr (Or.inr (Or.inr ⟨c', hcov, rfl⟩)))
        (ihc (Or.inl hhorn))
    · rcases covBy_le_cases hcov hc'' with hle | rfl
      · exact .orTrueLeft (hor c) ((hleft c _).mpr (Or.inr (Or.inr ⟨c', hcov, rfl⟩)))
          (ihc (Or.inr ⟨c'', hle, hcl, hnp, hneg⟩))
      · exact hgoal c'' hcl hnp hneg

end Build

/-! ### Inverting a derivation

Whatever the circuit derives on the true rail, it derives for the intended
reason: the wiring leaves a gate no other input to have derived it from. -/

section Invert

variable {m M : A}

/-- The intended value of a point, by tag. The constant `1` carries no
information and the constant `0` is never derived, which is what makes the
induction go through. -/
def Val (p : cvpInterp.Map A) : Prop :=
  match p.1 with
  | .tt => True
  | .ff => False
  | .bd => BdVal (p.2 0) (p.2 1) (p.2 2)
  | .bdTop => BdTopVal (p.2 0) (p.2 1)
  | .hd => HdVal (p.2 0) (p.2 1) (p.2 2)
  | .gl => GlVal (p.2 0)

/-- **Nothing else evaluates to `1`.** By induction on the derivation: every
rule that can fire at a gate of the drawn circuit fires for the intended
reason. The false rail carries no information and is not tracked. -/
theorem val_of_gateVal (hm : ∀ a : A, m ≤ a) (hM : ∀ a : A, a ≤ M) :
    ∀ {b : Bool} {p : cvpInterp.Map A}, GateVal b p → b = true → Val p := by
  intro b p h
  induction h with
  | @constTrue g hg =>
    obtain ⟨t, w⟩ := g
    obtain ⟨rfl, -, -, -⟩ := (isTrue_iff t w).mp hg
    exact fun _ => trivial
  | @constFalse g hg => simp
  | @andTrue g l r hg hl hr _ _ ihl ihr =>
    intro _
    obtain ⟨t, w⟩ := g
    rcases (isAnd_iff t w).mp hg with rfl | ⟨rfl, -⟩
    · -- a conjunction chain: its right input forces the literal at hand
      have hcur : NegIn (w 0) (w 1) → ForcedIn (orank (w 2)) (w 1) := by
        intro hneg
        rcases (right_bd hm hM w r).mp hr with ⟨hn, -⟩ | ⟨-, -, rfl⟩ | ⟨-, s', hcov, rfl⟩
        · exact absurd hneg hn
        · exact (ihr rfl).elim
        · rw [orank_covBy hcov]
          exact (hdVal_top hM (w 1) s').mp (ihr rfl)
      rcases (left_bd hm w l).mp hl with ⟨hmin, rfl⟩ | ⟨y', hcov, rfl⟩
      · intro y' hy' hneg
        rw [le_antisymm hy' (hmin y')]
        exact hcur (by rwa [le_antisymm hy' (hmin y')] at hneg)
      · intro y'' hy'' hneg
        rcases covBy_le_cases hcov hy'' with hle | rfl
        · exact ihl rfl y'' hle hneg
        · exact hcur hneg
    · -- the top-stage conjunction chain, the same walk read at the fixed point
      have hcur : NegIn (w 0) (w 1) → Forced (w 1) := by
        intro hneg
        rcases (right_bdTop hm hM w r (by
          rcases (isAnd_iff (CvpTag.bdTop) w).mp hg with h | ⟨-, h2⟩
          · exact absurd h (by simp)
          · exact h2)).mp hr with ⟨hn, -⟩ | ⟨-, rfl⟩
        · exact absurd hneg hn
        · exact (forced_iff_top hM (w 1)).mpr ((hdVal_top hM (w 1) M).mp (ihr rfl))
      rcases (left_bdTop hm w l).mp hl with ⟨-, hmin, rfl⟩ | ⟨-, y', hcov, rfl⟩
      · intro y' hy' hneg
        rw [le_antisymm hy' (hmin y')]
        exact hcur (by rwa [le_antisymm hy' (hmin y')] at hneg)
      · intro y'' hy'' hneg
        rcases covBy_le_cases hcov hy'' with hle | rfl
        · exact ihl rfl y'' hle hneg
        · exact hcur hneg
  | @andFalseLeft g l hg hl _ ihl => simp
  | @andFalseRight g r hg hr _ ihr => simp
  | @orTrueLeft g l hg hl _ ihl =>
    intro _
    obtain ⟨t, w⟩ := g
    rcases (isOr_iff t w).mp hg with rfl | ⟨rfl, h1, h2⟩
    · rcases (left_hd hm w l).mp hl with ⟨-, rfl⟩ | ⟨c', hcov, rfl⟩
      · exact (ihl rfl).elim
      · obtain ⟨c'', hle, hrest⟩ := ihl rfl
        exact ⟨c'', hle.trans hcov.le, hrest⟩
    · rcases (left_gl hm w l h1 h2).mp hl with ⟨-, -, rfl⟩ | ⟨-, hhorn, rfl⟩ | ⟨c', hcov, rfl⟩
      · exact (ihl rfl).elim
      · exact Or.inl hhorn
      · rcases ihl rfl with hhorn | ⟨c'', hle, hrest⟩
        · exact Or.inl hhorn
        · exact Or.inr ⟨c'', hle.trans hcov.le, hrest⟩
  | @orTrueRight g r hg hr _ ihr =>
    intro _
    obtain ⟨t, w⟩ := g
    rcases (isOr_iff t w).mp hg with rfl | ⟨rfl, h1, h2⟩
    · rcases (right_hd hm hM w r).mp hr with ⟨⟨hcl, hp⟩, rfl⟩ | ⟨-, rfl⟩
      · exact ⟨w 1, le_rfl, hcl, hp, (bdVal_top hM (w 1) (w 2)).mp (ihr rfl)⟩
      · exact (ihr rfl).elim
    · rcases (right_gl hm hM w r h1 h2).mp hr with ⟨⟨hcl, hnp⟩, rfl⟩ | ⟨-, rfl⟩
      · exact Or.inr ⟨w 0, le_rfl, hcl, hnp, fun y hn => ihr rfl y (hM y) hn⟩
      · exact (ihr rfl).elim
  | @orFalse g l r hg hl hr _ _ ihl ihr => simp
  | @notTrue g i hg hi _ ihi =>
    obtain ⟨t, w⟩ := g
    exact absurd hg (not_isNot t w)
  | @notFalse g i hg hi _ ihi => simp

end Invert

end CvpVal

end DescriptiveComplexity
