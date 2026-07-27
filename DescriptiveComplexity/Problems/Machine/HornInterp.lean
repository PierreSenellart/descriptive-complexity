/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.HornHardness
import DescriptiveComplexity.Problems.Machine.Interp

/-!
# The transcription: `HORNSAT ≤ᶠᵒ[≤] DTMAccept`

The first-order half of stage 4 of the machine bridge: the defining formulas
of an interpretation of `Language.turing` in ordered CNF instances describing
the unit-propagation machine of
`DescriptiveComplexity.Problems.Machine.HornHardness`, shown to realize exactly its
predicates, and bundled as the ordered reduction
`DescriptiveComplexity.HornTM.hornSat_ordered_fo_reduction_dtmAccept`.

The method is stage 3's (`DescriptiveComplexity.Problems.Machine.Interp`), one
dimension up: three shape helpers – `cstHF`, `oneHF`, `twoHF` – for the three
payload shapes of the machine's elements, each with one realization lemma
taking the valuation abstractly, so that every defining formula matches on its
*first* tag only and every characterization case discharges by `rfl`. The two
relational destinations (`tMarkEndRound`/`tMarkEndVer` dispatch to the lowest
clause, which is not in their payload) get bespoke min-clause-pinned helpers.
The clause-order formulas (`minClF`, `maxClF`, `nextClF`, `noClF`) are reused
from stage 3 unchanged; the element-order ones (`minF`, `maxF`, `succF`) come
from `DescriptiveComplexity.OrderWalk`, with a small bridge from `succF`'s
between-form to `DescriptiveComplexity.SuccElt`.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace HornTM

open Language Structure SatOcc SatTM

/-! ### Formula pieces -/

section Builders

variable {α : Type}

/-- `b` is the successor of `a` among the elements, as a formula: `succF`'s
between-form. -/
noncomputable def succEltF (x y : α) : satOrd.Formula α := succF x y

/-- The instance is Horn – at most one positive literal per clause – as a
sentence-shaped formula: the accept gate. -/
noncomputable def hornF : satOrd.Formula α :=
  Formula.iAlls (Fin 3)
    ((clF (Sum.inr 0) ⊓ posF (Sum.inr 0) (Sum.inr 1) ⊓ posF (Sum.inr 0) (Sum.inr 2)) ⟹
      eqF (Sum.inr 1) (Sum.inr 2))

/-- The literal test of the verification phase, for the statically known mark
`b`. -/
noncomputable def mLitF (b : Bool) : satOrd.Formula (Fin 2 × Fin 3) :=
  if b then posF (0, 0) (0, 1) else negF (0, 0) (0, 1)

end Builders

section BuilderRealize

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {α : Type} {v : α → A}

theorem realize_succEltF {x y : α} {a b : A} (hx : v x = a) (hy : v y = b) :
    (succEltF x y).Realize v ↔ SuccElt a b := by
  rw [succEltF, realize_succF, hx, hy, SuccElt]
  refine and_congr Iff.rfl ⟨fun h z hz => ?_, fun h z hz => ?_⟩
  · by_contra hcon
    exact h z ⟨hz, lt_of_not_ge hcon⟩
  · exact absurd (h z hz.1) (not_le.mpr hz.2)

theorem realize_hornF : (hornF (α := α)).Realize v ↔ AtMostOnePositive A := by
  simp only [hornF, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf,
    realize_clF, realize_posF, realize_eqF, Sum.elim_inr, AtMostOnePositive]
  exact ⟨fun h c x y hc hx hy => h ![c, x, y] ⟨⟨hc, hx⟩, hy⟩,
    fun h i hi => h (i 0) (i 1) (i 2) hi.1.1 hi.1.2 hi.2⟩

theorem realize_mLitF {b : Bool} {c x : A} {v : Fin 2 × Fin 3 → A}
    (h0 : v (0, 0) = c) (h1 : v (0, 1) = x) :
    (mLitF b).Realize v ↔ MLit c x b := by
  cases b
  · rw [mLitF, if_neg Bool.false_ne_true]
    simp only [realize_negF, h0, h1, MLit, SatPos, SatNeg, SatOcc.NegIn]
    simp
  · rw [mLitF, if_pos rfl]
    simp only [realize_posF, h0, h1, MLit, SatPos, SatNeg, SatOcc.PosIn]
    simp

end BuilderRealize

/-! ### The three shapes, as formulas -/

section Shapes

/-- The second argument is the constant `cstH s`. -/
noncomputable def cstHF (s t' : UPTag) : satOrd.Formula (Fin 2 × Fin 3) :=
  if t' = s then minF (1, 0) ⊓ minF (1, 1) ⊓ minF (1, 2) else ⊥

/-- The second argument is `oneH s (v x)`. -/
noncomputable def oneHF (s : UPTag) (x : Fin 2 × Fin 3) (t' : UPTag) :
    satOrd.Formula (Fin 2 × Fin 3) :=
  if t' = s then eqF (1, 0) x ⊓ minF (1, 1) ⊓ minF (1, 2) else ⊥

/-- The second argument is `twoH s (v x) (v y)`. -/
noncomputable def twoHF (s : UPTag) (x y : Fin 2 × Fin 3) (t' : UPTag) :
    satOrd.Formula (Fin 2 × Fin 3) :=
  if t' = s then eqF (1, 0) x ⊓ eqF (1, 1) y ⊓ minF (1, 2) else ⊥

/-- The second argument is a check state of the round held by `x` and the
lowest clause: the destination of a round turn. -/
noncomputable def roundDstF (x : Fin 2 × Fin 3) (t' : UPTag) :
    satOrd.Formula (Fin 2 × Fin 3) :=
  if t' = UPTag.qChk true then eqF (1, 0) x ⊓ minClF (1, 1) ⊓ minF (1, 2) else ⊥

/-- The second argument is the initial verification state of the lowest
clause: the destination of the turn into verification. -/
noncomputable def verDstF (t' : UPTag) : satOrd.Formula (Fin 2 × Fin 3) :=
  if t' = UPTag.qVer false true then minClF (1, 0) ⊓ minF (1, 1) ⊓ minF (1, 2) else ⊥

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
variable {v : Fin 2 × Fin 3 → A}

theorem realize_cstHF {s : UPTag} {q : HV A}
    (h0 : v (1, 0) = q.2 0) (h1 : v (1, 1) = q.2 1) (h2 : v (1, 2) = q.2 2) :
    (cstHF s q.1).Realize v ↔ q = cstH s := by
  rw [cstHF]
  by_cases hs : q.1 = s
  · rw [if_pos hs]
    simp only [Formula.realize_inf, realize_minF, h0, h1, h2]
    constructor
    · rintro ⟨⟨ha, hb⟩, hc⟩
      exact hV_ext hs (le_antisymm (ha botA) (botA_le _)) (le_antisymm (hb botA) (botA_le _))
        (le_antisymm (hc botA) (botA_le _))
    · rintro rfl
      exact ⟨⟨fun a => botA_le a, fun a => botA_le a⟩, fun a => botA_le a⟩
  · rw [if_neg hs]
    simp only [Formula.realize_bot, false_iff]
    exact fun hq => hs (congrArg Prod.fst hq)

theorem realize_oneHF {s : UPTag} {x : Fin 2 × Fin 3} {q : HV A}
    (h0 : v (1, 0) = q.2 0) (h1 : v (1, 1) = q.2 1) (h2 : v (1, 2) = q.2 2) :
    (oneHF s x q.1).Realize v ↔ q = oneH s (v x) := by
  rw [oneHF]
  by_cases hs : q.1 = s
  · rw [if_pos hs]
    simp only [Formula.realize_inf, realize_eqF, realize_minF, h0, h1, h2]
    constructor
    · rintro ⟨⟨ha, hb⟩, hc⟩
      exact hV_ext hs ha (le_antisymm (hb botA) (botA_le _)) (le_antisymm (hc botA) (botA_le _))
    · rintro rfl
      exact ⟨⟨rfl, fun a => botA_le a⟩, fun a => botA_le a⟩
  · rw [if_neg hs]
    simp only [Formula.realize_bot, false_iff]
    exact fun hq => hs (congrArg Prod.fst hq)

theorem realize_twoHF {s : UPTag} {x y : Fin 2 × Fin 3} {q : HV A}
    (h0 : v (1, 0) = q.2 0) (h1 : v (1, 1) = q.2 1) (h2 : v (1, 2) = q.2 2) :
    (twoHF s x y q.1).Realize v ↔ q = twoH s (v x) (v y) := by
  rw [twoHF]
  by_cases hs : q.1 = s
  · rw [if_pos hs]
    simp only [Formula.realize_inf, realize_eqF, realize_minF, h0, h1, h2]
    constructor
    · rintro ⟨⟨ha, hb⟩, hc⟩
      exact hV_ext hs ha hb (le_antisymm (hc botA) (botA_le _))
    · rintro rfl
      exact ⟨⟨rfl, rfl⟩, fun a => botA_le a⟩
  · rw [if_neg hs]
    simp only [Formula.realize_bot, false_iff]
    exact fun hq => hs (congrArg Prod.fst hq)

omit [Finite A] [Nonempty A] in
theorem realize_roundDstF {x : Fin 2 × Fin 3} {q : HV A}
    (h0 : v (1, 0) = q.2 0) (h1 : v (1, 1) = q.2 1) (h2 : v (1, 2) = q.2 2) :
    (roundDstF x q.1).Realize v ↔
      (q.1 = UPTag.qChk true ∧ q.2 0 = v x ∧ SatMinCl (q.2 1) ∧ ∀ a : A, q.2 2 ≤ a) := by
  rw [roundDstF]
  by_cases hs : q.1 = UPTag.qChk true
  · rw [if_pos hs]
    simp only [Formula.realize_inf, realize_eqF, realize_minF, realize_minClF h1, h0, h2]
    exact ⟨fun ⟨⟨ha, hb⟩, hc⟩ => ⟨hs, ha, hb, hc⟩, fun ⟨_, ha, hb, hc⟩ => ⟨⟨ha, hb⟩, hc⟩⟩
  · rw [if_neg hs]
    simp only [Formula.realize_bot, false_iff]
    exact fun hq => hs hq.1

omit [Finite A] [Nonempty A] in
theorem realize_verDstF {q : HV A}
    (h0 : v (1, 0) = q.2 0) (h1 : v (1, 1) = q.2 1) (h2 : v (1, 2) = q.2 2) :
    (verDstF q.1).Realize v ↔
      (q.1 = UPTag.qVer false true ∧ SatMinCl (q.2 0) ∧ (∀ a : A, q.2 1 ≤ a) ∧
        ∀ a : A, q.2 2 ≤ a) := by
  rw [verDstF]
  by_cases hs : q.1 = UPTag.qVer false true
  · rw [if_pos hs]
    simp only [Formula.realize_inf, realize_minF, realize_minClF h0, h1, h2]
    exact ⟨fun ⟨⟨ha, hb⟩, hc⟩ => ⟨hs, ha, hb, hc⟩, fun ⟨_, ha, hb, hc⟩ => ⟨⟨ha, hb⟩, hc⟩⟩
  · rw [if_neg hs]
    simp only [Formula.realize_bot, false_iff]
    exact fun hq => hs hq.1

end Shapes

/-! ### The defining formulas -/

/-- Defining formula for `posn`. -/
noncomputable def hPosnF : UPTag → satOrd.Formula (Fin 1 × Fin 3)
  | .pStart => minF (0, 0) ⊓ minF (0, 1) ⊓ minF (0, 2)
  | .pCell => minF (0, 1) ⊓ minF (0, 2)
  | .pEnd => minF (0, 0) ⊓ minF (0, 1) ⊓ minF (0, 2)
  | .pFill _ => ⊤
  | _ => ⊥

/-- Defining formula for `tr`: the payload promises of `HTr`. -/
noncomputable def hTrF : UPTag → satOrd.Formula (Fin 1 × Fin 3)
  | .tInitChk => minF (0, 0) ⊓ minClF (0, 1) ⊓ minF (0, 2)
  | .tInitAcc => (minF (0, 0) ⊓ minF (0, 1) ⊓ minF (0, 2)) ⊓ noClF
  | .tChk _ _ => clF (0, 1)
  | .tChkEnd _ => clF (0, 1) ⊓ minF (0, 2)
  | .tMark _ _ => clF (0, 1)
  | .tMarkEndNext _ => nextClF (0, 1) (0, 2)
  | .tMarkEndRound _ => succEltF (0, 0) (0, 1) ⊓ maxClF (0, 2)
  | .tMarkEndVer _ => maxF (0, 0) ⊓ maxClF (0, 1) ⊓ minF (0, 2)
  | .tVer _ _ _ => clF (0, 0) ⊓ minF (0, 2)
  | .tVerNext _ => nextClF (0, 0) (0, 1) ⊓ minF (0, 2)
  | .tVerAcc _ => maxClF (0, 0) ⊓ minF (0, 1) ⊓ minF (0, 2) ⊓ hornF
  | _ => ⊥

/-- Defining formula for `start`. -/
noncomputable def hStartF : UPTag → satOrd.Formula (Fin 1 × Fin 3)
  | .qInit => minF (0, 0) ⊓ minF (0, 1) ⊓ minF (0, 2)
  | _ => ⊥

/-- Defining formula for `acc`. -/
noncomputable def hAccF : UPTag → satOrd.Formula (Fin 1 × Fin 3)
  | .qAcc => ⊤
  | _ => ⊥

/-- Defining formula for `blank`. -/
noncomputable def hBlankF : UPTag → satOrd.Formula (Fin 1 × Fin 3)
  | .sBlank => minF (0, 0) ⊓ minF (0, 1) ⊓ minF (0, 2)
  | _ => ⊥

/-- Defining formula for `right`. -/
noncomputable def hRightF : UPTag → satOrd.Formula (Fin 1 × Fin 3)
  | .tInitChk => ⊤
  | .tInitAcc => ⊤
  | .tChk _ _ => ⊤
  | .tMarkEndNext _ => ⊤
  | .tMarkEndRound _ => ⊤
  | .tMarkEndVer _ => ⊤
  | .tVer _ _ d => if d then ⊤ else ⊥
  | .tVerNext d => if d then ⊥ else ⊤
  | .tVerAcc d => if d then ⊥ else ⊤
  | _ => ⊥

/-- Defining formula for `inp`. -/
noncomputable def hInpF : UPTag → UPTag → satOrd.Formula (Fin 2 × Fin 3)
  | .pStart, t' => cstHF .sStart t'
  | .pCell, t' => oneHF .sU (0, 0) t'
  | .pEnd, t' => cstHF .sEnd t'
  | _, _ => ⊥

/-- Defining formula for `tsrc`. -/
noncomputable def hSrcF : UPTag → UPTag → satOrd.Formula (Fin 2 × Fin 3)
  | .tInitChk, t' => cstHF .qInit t'
  | .tInitAcc, t' => cstHF .qInit t'
  | .tChk _ f, t' => twoHF (.qChk f) (0, 0) (0, 1) t'
  | .tChkEnd f, t' => twoHF (.qChk f) (0, 0) (0, 1) t'
  | .tMark _ mrk, t' => twoHF (.qMark mrk) (0, 0) (0, 1) t'
  | .tMarkEndNext mrk, t' => twoHF (.qMark mrk) (0, 0) (0, 1) t'
  | .tMarkEndRound mrk, t' => twoHF (.qMark mrk) (0, 0) (0, 2) t'
  | .tMarkEndVer mrk, t' => twoHF (.qMark mrk) (0, 0) (0, 1) t'
  | .tVer _ f d, t' => oneHF (.qVer f d) (0, 0) t'
  | .tVerNext d, t' => oneHF (.qVer true d) (0, 0) t'
  | .tVerAcc d, t' => oneHF (.qVer true d) (0, 0) t'
  | _, _ => ⊥

/-- Defining formula for `tread`. -/
noncomputable def hReadF : UPTag → UPTag → satOrd.Formula (Fin 2 × Fin 3)
  | .tInitChk, t' => cstHF .sStart t'
  | .tInitAcc, t' => cstHF .sStart t'
  | .tChk m _, t' => oneHF (if m then .sM else .sU) (0, 2) t'
  | .tChkEnd _, t' => cstHF .sEnd t'
  | .tMark m _, t' => oneHF (if m then .sM else .sU) (0, 2) t'
  | .tMarkEndNext _, t' => cstHF .sStart t'
  | .tMarkEndRound _, t' => cstHF .sStart t'
  | .tMarkEndVer _, t' => cstHF .sStart t'
  | .tVer m _ _, t' => oneHF (if m then .sM else .sU) (0, 1) t'
  | .tVerNext d, t' => cstHF (if d then .sEnd else .sStart) t'
  | .tVerAcc d, t' => cstHF (if d then .sEnd else .sStart) t'
  | _, _ => ⊥

/-- Defining formula for `tdst`. -/
noncomputable def hDstF : UPTag → UPTag → satOrd.Formula (Fin 2 × Fin 3)
  | .tInitChk, t' => twoHF (.qChk true) (0, 0) (0, 1) t'
  | .tInitAcc, t' => cstHF .qAcc t'
  | .tChk m f, t' =>
      (twoHF (.qChk true) (0, 0) (0, 1) t' ⊓
        (if f then (if m then ⊤ else ∼(negF (0, 1) (0, 2))) else ⊥)) ⊔
        (twoHF (.qChk false) (0, 0) (0, 1) t' ⊓
          (if f then (if m then ⊥ else negF (0, 1) (0, 2)) else ⊤))
  | .tChkEnd f, t' => twoHF (.qMark f) (0, 0) (0, 1) t'
  | .tMark _ mrk, t' => twoHF (.qMark mrk) (0, 0) (0, 1) t'
  | .tMarkEndNext _, t' => twoHF (.qChk true) (0, 0) (0, 2) t'
  | .tMarkEndRound _, t' => roundDstF (0, 1) t'
  | .tMarkEndVer _, t' => verDstF t'
  | .tVer m f d, t' =>
      (oneHF (.qVer true d) (0, 0) t' ⊓ (if f then ⊤ else mLitF m)) ⊔
        (oneHF (.qVer false d) (0, 0) t' ⊓ (if f then ⊥ else ∼(mLitF m)))
  | .tVerNext d, t' => oneHF (.qVer false (!d)) (0, 1) t'
  | .tVerAcc _, t' => cstHF .qAcc t'
  | _, _ => ⊥

/-- Defining formula for `twrite`. -/
noncomputable def hWriteF : UPTag → UPTag → satOrd.Formula (Fin 2 × Fin 3)
  | .tInitChk, t' => cstHF .sStart t'
  | .tInitAcc, t' => cstHF .sStart t'
  | .tChk m _, t' => oneHF (if m then .sM else .sU) (0, 2) t'
  | .tChkEnd _, t' => cstHF .sEnd t'
  | .tMark m mrk, t' =>
      (oneHF .sM (0, 2) t' ⊓ (if mrk then posF (0, 1) (0, 2) else ⊥)) ⊔
        (oneHF (if m then .sM else .sU) (0, 2) t' ⊓
          (if mrk then ∼(posF (0, 1) (0, 2)) else ⊤))
  | .tMarkEndNext _, t' => cstHF .sStart t'
  | .tMarkEndRound _, t' => cstHF .sStart t'
  | .tMarkEndVer _, t' => cstHF .sStart t'
  | .tVer m _ _, t' => oneHF (if m then .sM else .sU) (0, 1) t'
  | .tVerNext d, t' => cstHF (if d then .sEnd else .sStart) t'
  | .tVerAcc d, t' => cstHF (if d then .sEnd else .sStart) t'
  | _, _ => ⊥

/-- **The interpretation of machine instances in ordered CNF instances**,
describing the unit-propagation machine. -/
noncomputable def hornTuringInterp : FOInterpretation satOrd Language.turing UPTag 3 where
  relFormula {n} R :=
    match n, R with
    | _, .posn => fun t => hPosnF (t 0)
    | _, .tr => fun t => hTrF (t 0)
    | _, .start => fun t => hStartF (t 0)
    | _, .acc => fun t => hAccF (t 0)
    | _, .blank => fun t => hBlankF (t 0)
    | _, .right => fun t => hRightF (t 0)
    | _, .le => fun t => lexLeF Language.sat 3 (t 0) (t 1)
    | _, .tsrc => fun t => hSrcF (t 0) (t 1)
    | _, .tread => fun t => hReadF (t 0) (t 1)
    | _, .tdst => fun t => hDstF (t 0) (t 1)
    | _, .twrite => fun t => hWriteF (t 0) (t 1)
    | _, .inp => fun t => hInpF (t 0) (t 1)

/-! ### The realization lemmas -/

section Characterize

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- The identity equivalence between the tagged triples and the interpreted
universe. -/
def hornMapEquiv : HV A ≃ hornTuringInterp.Map A := Equiv.refl (HV A)

omit [Finite A] [Nonempty A] in
theorem relMap_posn (p : HV A) : TMPosn (hornMapEquiv p) ↔ HPosn p := by
  rw [TMPosn, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  have hmin3 : ∀ v : Fin 1 × Fin 3 → A, v (0, 0) = w 0 → v (0, 1) = w 1 → v (0, 2) = w 2 →
      ((minF (0, 0) ⊓ minF (0, 1) ⊓ minF (0, 2) : satOrd.Formula (Fin 1 × Fin 3)).Realize v ↔
        IsMinTup3 w) := by
    intro v h0 h1 h2
    simp only [Formula.realize_inf, realize_minF, h0, h1, h2, IsMinTup3, and_assoc]
  cases t
  case pStart => exact hmin3 _ rfl rfl rfl
  case pCell =>
    have key : ∀ v : Fin 1 × Fin 3 → A, v (0, 1) = w 1 → v (0, 2) = w 2 →
        ((minF (0, 1) ⊓ minF (0, 2) : satOrd.Formula (Fin 1 × Fin 3)).Realize v ↔
          ((∀ a : A, w 1 ≤ a) ∧ ∀ a : A, w 2 ≤ a)) := by
      intro v h1 h2
      simp only [Formula.realize_inf, realize_minF, h1, h2]
    exact key _ rfl rfl
  case pEnd => exact hmin3 _ rfl rfl rfl
  case pFill _ => exact iff_of_true (Formula.realize_top.mpr trivial) trivial
  all_goals exact Iff.rfl

omit [Finite A] [Nonempty A] in
theorem relMap_tr (p : HV A) : TMTr (hornMapEquiv p) ↔ HTr p := by
  rw [TMTr, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case tInitChk =>
    have key : ∀ v : Fin 1 × Fin 3 → A, v (0, 0) = w 0 → v (0, 1) = w 1 → v (0, 2) = w 2 →
        ((minF (0, 0) ⊓ minClF (0, 1) ⊓ minF (0, 2) :
            satOrd.Formula (Fin 1 × Fin 3)).Realize v ↔
          (MinElt (w 0) ∧ SatMinCl (w 1) ∧ ∀ a : A, w 2 ≤ a)) := by
      intro v h0 h1 h2
      simp only [Formula.realize_inf, realize_minF, realize_minClF h1, h0, h2, and_assoc,
        MinElt]
    exact key _ rfl rfl rfl
  case tInitAcc =>
    have key : ∀ v : Fin 1 × Fin 3 → A, v (0, 0) = w 0 → v (0, 1) = w 1 → v (0, 2) = w 2 →
        (((minF (0, 0) ⊓ minF (0, 1) ⊓ minF (0, 2)) ⊓ noClF :
            satOrd.Formula (Fin 1 × Fin 3)).Realize v ↔
          (IsMinTup3 w ∧ ∀ e : A, ¬ SatCl e)) := by
      intro v h0 h1 h2
      simp only [Formula.realize_inf, realize_minF, realize_noClF, h0, h1, h2, IsMinTup3,
        and_assoc]
    exact key _ rfl rfl rfl
  case tChk m f => exact realize_clF.trans Iff.rfl
  case tChkEnd f =>
    have key : ∀ v : Fin 1 × Fin 3 → A, v (0, 1) = w 1 → v (0, 2) = w 2 →
        ((clF (0, 1) ⊓ minF (0, 2) : satOrd.Formula (Fin 1 × Fin 3)).Realize v ↔
          (SatCl (w 1) ∧ ∀ a : A, w 2 ≤ a)) := by
      intro v h1 h2
      simp only [Formula.realize_inf, realize_clF, realize_minF, h1, h2, SatCl,
        SatOcc.IsCl]
    exact key _ rfl rfl
  case tMark m mrk => exact realize_clF.trans Iff.rfl
  case tMarkEndNext mrk => exact realize_nextClF rfl rfl
  case tMarkEndRound mrk =>
    have key : ∀ v : Fin 1 × Fin 3 → A, v (0, 0) = w 0 → v (0, 1) = w 1 → v (0, 2) = w 2 →
        ((succEltF (0, 0) (0, 1) ⊓ maxClF (0, 2) :
            satOrd.Formula (Fin 1 × Fin 3)).Realize v ↔
          (SuccElt (w 0) (w 1) ∧ SatMaxCl (w 2))) := by
      intro v h0 h1 h2
      rw [Formula.realize_inf, realize_succEltF h0 h1, realize_maxClF h2]
    exact key _ rfl rfl rfl
  case tMarkEndVer mrk =>
    have key : ∀ v : Fin 1 × Fin 3 → A, v (0, 0) = w 0 → v (0, 1) = w 1 → v (0, 2) = w 2 →
        ((maxF (0, 0) ⊓ maxClF (0, 1) ⊓ minF (0, 2) :
            satOrd.Formula (Fin 1 × Fin 3)).Realize v ↔
          (MaxElt (w 0) ∧ SatMaxCl (w 1) ∧ ∀ a : A, w 2 ≤ a)) := by
      intro v h0 h1 h2
      simp only [Formula.realize_inf, realize_maxF, realize_maxClF h1, realize_minF, h0, h2,
        and_assoc, MaxElt]
    exact key _ rfl rfl rfl
  case tVer m f d =>
    have key : ∀ v : Fin 1 × Fin 3 → A, v (0, 0) = w 0 → v (0, 2) = w 2 →
        ((clF (0, 0) ⊓ minF (0, 2) : satOrd.Formula (Fin 1 × Fin 3)).Realize v ↔
          (SatCl (w 0) ∧ ∀ a : A, w 2 ≤ a)) := by
      intro v h0 h2
      simp only [Formula.realize_inf, realize_clF, realize_minF, h0, h2, SatCl,
        SatOcc.IsCl]
    exact key _ rfl rfl
  case tVerNext d =>
    have key : ∀ v : Fin 1 × Fin 3 → A, v (0, 0) = w 0 → v (0, 1) = w 1 → v (0, 2) = w 2 →
        ((nextClF (0, 0) (0, 1) ⊓ minF (0, 2) :
            satOrd.Formula (Fin 1 × Fin 3)).Realize v ↔
          (SatNextCl (w 0) (w 1) ∧ ∀ a : A, w 2 ≤ a)) := by
      intro v h0 h1 h2
      rw [Formula.realize_inf, realize_nextClF h0 h1]
      simp only [realize_minF, h2]
    exact key _ rfl rfl rfl
  case tVerAcc d =>
    have key : ∀ v : Fin 1 × Fin 3 → A, v (0, 0) = w 0 → v (0, 1) = w 1 → v (0, 2) = w 2 →
        ((maxClF (0, 0) ⊓ minF (0, 1) ⊓ minF (0, 2) ⊓ hornF :
            satOrd.Formula (Fin 1 × Fin 3)).Realize v ↔
          (SatMaxCl (w 0) ∧ (∀ a : A, w 1 ≤ a) ∧ (∀ a : A, w 2 ≤ a) ∧
            AtMostOnePositive A)) := by
      intro v h0 h1 h2
      simp only [Formula.realize_inf, realize_maxClF h0, realize_minF, realize_hornF, h1, h2,
        and_assoc]
    exact key _ rfl rfl rfl
  all_goals exact Iff.rfl

omit [Finite A] [Nonempty A] in
theorem relMap_start (p : HV A) : TMStart (hornMapEquiv p) ↔ HStart p := by
  rw [TMStart, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  have hmin3 : ∀ v : Fin 1 × Fin 3 → A, v (0, 0) = w 0 → v (0, 1) = w 1 → v (0, 2) = w 2 →
      ((minF (0, 0) ⊓ minF (0, 1) ⊓ minF (0, 2) : satOrd.Formula (Fin 1 × Fin 3)).Realize v ↔
        IsMinTup3 w) := by
    intro v h0 h1 h2
    simp only [Formula.realize_inf, realize_minF, h0, h1, h2, IsMinTup3, and_assoc]
  cases t
  case qInit => exact (hmin3 _ rfl rfl rfl).trans ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  all_goals exact iff_of_false (by exact fun h => h) (fun h => UPTag.noConfusion h.1)

omit [Finite A] [Nonempty A] in
theorem relMap_acc (p : HV A) : TMAcc (hornMapEquiv p) ↔ HAcc p := by
  rw [TMAcc, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case qAcc => exact iff_of_true (Formula.realize_top.mpr trivial) rfl
  all_goals exact iff_of_false (by exact fun h => h) (fun h => UPTag.noConfusion h)

omit [Finite A] [Nonempty A] in
theorem relMap_blank (p : HV A) : TMBlank (hornMapEquiv p) ↔ HBlank p := by
  rw [TMBlank, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  have hmin3 : ∀ v : Fin 1 × Fin 3 → A, v (0, 0) = w 0 → v (0, 1) = w 1 → v (0, 2) = w 2 →
      ((minF (0, 0) ⊓ minF (0, 1) ⊓ minF (0, 2) : satOrd.Formula (Fin 1 × Fin 3)).Realize v ↔
        IsMinTup3 w) := by
    intro v h0 h1 h2
    simp only [Formula.realize_inf, realize_minF, h0, h1, h2, IsMinTup3, and_assoc]
  cases t
  case sBlank => exact (hmin3 _ rfl rfl rfl).trans ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  all_goals exact iff_of_false (by exact fun h => h) (fun h => UPTag.noConfusion h.1)

omit [Finite A] [Nonempty A] in
theorem relMap_right (p : HV A) : TMRight (hornMapEquiv p) ↔ HRight p := by
  rw [TMRight, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case tInitChk => exact iff_of_true (Formula.realize_top.mpr trivial) trivial
  case tInitAcc => exact iff_of_true (Formula.realize_top.mpr trivial) trivial
  case tChk m f => exact iff_of_true (Formula.realize_top.mpr trivial) trivial
  case tMarkEndNext mrk => exact iff_of_true (Formula.realize_top.mpr trivial) trivial
  case tMarkEndRound mrk => exact iff_of_true (Formula.realize_top.mpr trivial) trivial
  case tMarkEndVer mrk => exact iff_of_true (Formula.realize_top.mpr trivial) trivial
  case tVer m f d =>
    cases d
    · exact iff_of_false (by exact fun h => h) (fun h => Bool.noConfusion h)
    · exact iff_of_true (Formula.realize_top.mpr trivial) rfl
  case tVerNext d =>
    cases d
    · exact iff_of_true (Formula.realize_top.mpr trivial) rfl
    · exact iff_of_false (by exact fun h => h) (fun h => Bool.noConfusion h)
  case tVerAcc d =>
    cases d
    · exact iff_of_true (Formula.realize_top.mpr trivial) rfl
    · exact iff_of_false (by exact fun h => h) (fun h => Bool.noConfusion h)
  all_goals exact Iff.rfl

omit [Finite A] [Nonempty A] in
theorem relMap_le (p q : HV A) :
    TMLe (hornMapEquiv p) (hornMapEquiv q) ↔ tagTupleLe p q := by
  rw [TMLe, FOInterpretation.relMap_map]
  exact realize_lexLeF

theorem relMap_inp (p q : HV A) :
    TMInp (hornMapEquiv p) (hornMapEquiv q) ↔ HInp p q := by
  rw [TMInp, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case pStart =>
    refine (realize_cstHF rfl rfl rfl).trans ⟨fun h => ?_, ?_⟩
    · have h' : q = cstH UPTag.sStart := h
      exact Or.inl ⟨rfl, by rw [h']; exact rfl, by rw [h']; exact isMinTup3_bot⟩
    · rintro (⟨-, h1, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩)
      · exact Prod.ext h1 (isMinTup3_unique h2 isMinTup3_bot)
      · exact UPTag.noConfusion h
      · exact UPTag.noConfusion h
  case pCell =>
    refine (realize_oneHF rfl rfl rfl).trans ⟨fun h => ?_, ?_⟩
    · have h' : q = oneH UPTag.sU (w 0) := h
      exact Or.inr (Or.inl ⟨rfl, by rw [h']; exact rfl, by rw [h']; exact rfl,
        by rw [h']; exact fun b => botA_le b, by rw [h']; exact fun b => botA_le b⟩)
    · rintro (⟨h, -⟩ | ⟨-, h1, h2, h3, h4⟩ | ⟨h, -⟩)
      · exact UPTag.noConfusion h
      · exact hV_ext h1 h2 (le_antisymm (h3 botA) (botA_le _))
          (le_antisymm (h4 botA) (botA_le _))
      · exact UPTag.noConfusion h
  case pEnd =>
    refine (realize_cstHF rfl rfl rfl).trans ⟨fun h => ?_, ?_⟩
    · have h' : q = cstH UPTag.sEnd := h
      exact Or.inr (Or.inr ⟨rfl, by rw [h']; exact rfl, by rw [h']; exact isMinTup3_bot⟩)
    · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h1, h2⟩)
      · exact UPTag.noConfusion h
      · exact UPTag.noConfusion h
      · exact Prod.ext h1 (isMinTup3_unique h2 isMinTup3_bot)
  all_goals
    refine iff_of_false (by exact fun h => h) ?_
    rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact UPTag.noConfusion h

theorem relMap_tsrc (p q : HV A) :
    TMSrc (hornMapEquiv p) (hornMapEquiv q) ↔ HSrc p q := by
  rw [TMSrc, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case tInitChk => exact realize_cstHF rfl rfl rfl
  case tInitAcc => exact realize_cstHF rfl rfl rfl
  case tChk m f => exact realize_twoHF rfl rfl rfl
  case tChkEnd f => exact realize_twoHF rfl rfl rfl
  case tMark m mrk => exact realize_twoHF rfl rfl rfl
  case tMarkEndNext mrk => exact realize_twoHF rfl rfl rfl
  case tMarkEndRound mrk => exact realize_twoHF rfl rfl rfl
  case tMarkEndVer mrk => exact realize_twoHF rfl rfl rfl
  case tVer m f d => exact realize_oneHF rfl rfl rfl
  case tVerNext d => exact realize_oneHF rfl rfl rfl
  case tVerAcc d => exact realize_oneHF rfl rfl rfl
  all_goals exact Iff.rfl

theorem relMap_tread (p q : HV A) :
    TMRead (hornMapEquiv p) (hornMapEquiv q) ↔ HRead p q := by
  rw [TMRead, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case tInitChk => exact realize_cstHF rfl rfl rfl
  case tInitAcc => exact realize_cstHF rfl rfl rfl
  case tChk m f => exact realize_oneHF rfl rfl rfl
  case tChkEnd f => exact realize_cstHF rfl rfl rfl
  case tMark m mrk => exact realize_oneHF rfl rfl rfl
  case tMarkEndNext mrk => exact realize_cstHF rfl rfl rfl
  case tMarkEndRound mrk => exact realize_cstHF rfl rfl rfl
  case tMarkEndVer mrk => exact realize_cstHF rfl rfl rfl
  case tVer m f d => exact realize_oneHF rfl rfl rfl
  case tVerNext d => cases d <;> exact realize_cstHF rfl rfl rfl
  case tVerAcc d => cases d <;> exact realize_cstHF rfl rfl rfl
  all_goals exact Iff.rfl

theorem relMap_twrite (p q : HV A) :
    TMWrite (hornMapEquiv p) (hornMapEquiv q) ↔ HWrite p q := by
  rw [TMWrite, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case tInitChk => exact realize_cstHF rfl rfl rfl
  case tInitAcc => exact realize_cstHF rfl rfl rfl
  case tChk m f => exact realize_oneHF rfl rfl rfl
  case tChkEnd f => exact realize_cstHF rfl rfl rfl
  case tMark m mrk =>
    have key : ∀ v : Fin 2 × Fin 3 → A, v (0, 1) = w 1 → v (0, 2) = w 2 →
        v (1, 0) = q.2 0 → v (1, 1) = q.2 1 → v (1, 2) = q.2 2 →
        (((oneHF .sM (0, 2) q.1 ⊓ (if mrk then posF (0, 1) (0, 2) else ⊥)) ⊔
          (oneHF (if m then .sM else .sU) (0, 2) q.1 ⊓
            (if mrk then ∼(posF (0, 1) (0, 2)) else ⊤))).Realize v ↔
          ((q = symCell true (w 2) ∧ mrk = true ∧ SatPos (w 1) (w 2)) ∨
            (q = symCell m (w 2) ∧ (mrk = false ∨ ¬ SatPos (w 1) (w 2))))) := by
      intro v h1 h2 e0 e1 e2
      rw [Formula.realize_sup, Formula.realize_inf, Formula.realize_inf]
      have hq1 : (oneHF .sM (0, 2) q.1).Realize v ↔ q = symCell true (w 2) := by
        refine (realize_oneHF e0 e1 e2).trans ?_
        simp only [h2]
        try exact Iff.rfl
      have hq2 : (oneHF (if m then .sM else .sU) (0, 2) q.1).Realize v ↔
          q = symCell m (w 2) := by
        refine (realize_oneHF e0 e1 e2).trans ?_
        simp only [h2]
        try exact Iff.rfl
      have hpos : (posF (0, 1) (0, 2) : satOrd.Formula (Fin 2 × Fin 3)).Realize v ↔
          SatPos (w 1) (w 2) := by
        rw [realize_posF, h1, h2]
        exact Iff.rfl
      cases mrk
      · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
        refine or_congr ?_ (and_congr hq2 ?_)
        · rw [Formula.realize_bot]
          exact iff_of_false (fun h => h.2) (fun h => Bool.noConfusion h.2.1)
        · rw [Formula.realize_top]
          exact ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
      · rw [if_pos rfl, if_pos rfl, Formula.realize_not]
        refine or_congr (and_congr hq1 ?_) (and_congr hq2 ?_)
        · exact hpos.trans ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
        · exact (not_congr hpos).trans
            ⟨fun h => Or.inr h, fun h => h.resolve_left (fun hc => Bool.noConfusion hc)⟩
    exact key _ rfl rfl rfl rfl rfl
  case tMarkEndNext mrk => exact realize_cstHF rfl rfl rfl
  case tMarkEndRound mrk => exact realize_cstHF rfl rfl rfl
  case tMarkEndVer mrk => exact realize_cstHF rfl rfl rfl
  case tVer m f d => exact realize_oneHF rfl rfl rfl
  case tVerNext d => cases d <;> exact realize_cstHF rfl rfl rfl
  case tVerAcc d => cases d <;> exact realize_cstHF rfl rfl rfl
  all_goals exact Iff.rfl

theorem relMap_tdst (p q : HV A) :
    TMDst (hornMapEquiv p) (hornMapEquiv q) ↔ HDst p q := by
  rw [TMDst, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case tInitChk => exact realize_twoHF rfl rfl rfl
  case tInitAcc => exact realize_cstHF rfl rfl rfl
  case tChkEnd f => exact realize_twoHF rfl rfl rfl
  case tMark m mrk => exact realize_twoHF rfl rfl rfl
  case tMarkEndNext mrk => exact realize_twoHF rfl rfl rfl
  case tMarkEndRound mrk => exact realize_roundDstF rfl rfl rfl
  case tMarkEndVer mrk => exact realize_verDstF rfl rfl rfl
  case tVerNext d => exact realize_oneHF rfl rfl rfl
  case tVerAcc d => exact realize_cstHF rfl rfl rfl
  case tChk m f =>
    have key : ∀ v : Fin 2 × Fin 3 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
        v (0, 2) = w 2 → v (1, 0) = q.2 0 → v (1, 1) = q.2 1 → v (1, 2) = q.2 2 →
        (((twoHF (.qChk true) (0, 0) (0, 1) q.1 ⊓
            (if f then (if m then ⊤ else ∼(negF (0, 1) (0, 2))) else ⊥)) ⊔
          (twoHF (.qChk false) (0, 0) (0, 1) q.1 ⊓
            (if f then (if m then ⊥ else negF (0, 1) (0, 2)) else ⊤))).Realize v ↔
          ((q = stHChk true (w 0) (w 1) ∧ f = true ∧ (SatNeg (w 1) (w 2) → m = true)) ∨
            (q = stHChk false (w 0) (w 1) ∧
              (f = false ∨ (SatNeg (w 1) (w 2) ∧ m = false))))) := by
      intro v h0 h1 h2 e0 e1 e2
      rw [Formula.realize_sup, Formula.realize_inf, Formula.realize_inf]
      have htw₁ : (twoHF (.qChk true) (0, 0) (0, 1) q.1).Realize v ↔
          q = stHChk true (w 0) (w 1) := by
        refine (realize_twoHF e0 e1 e2).trans ?_
        simp only [h0, h1]
        try exact Iff.rfl
      have htw₂ : (twoHF (.qChk false) (0, 0) (0, 1) q.1).Realize v ↔
          q = stHChk false (w 0) (w 1) := by
        refine (realize_twoHF e0 e1 e2).trans ?_
        simp only [h0, h1]
        try exact Iff.rfl
      have hneg : (negF (0, 1) (0, 2) : satOrd.Formula (Fin 2 × Fin 3)).Realize v ↔
          SatNeg (w 1) (w 2) := by
        rw [realize_negF, h1, h2]
        exact Iff.rfl
      cases f
      · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
        refine or_congr ?_ (and_congr htw₂ ?_)
        · rw [Formula.realize_bot]
          exact iff_of_false (fun h => h.2) (fun h => Bool.noConfusion h.2.1)
        · rw [Formula.realize_top]
          exact ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
      · rw [if_pos rfl, if_pos rfl]
        cases m
        · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
            Formula.realize_not]
          refine or_congr (and_congr htw₁ ?_) (and_congr htw₂ ?_)
          · exact (not_congr hneg).trans
              ⟨fun hn => ⟨rfl, fun h => absurd h hn⟩,
                fun h hn => Bool.noConfusion (h.2 hn)⟩
          · exact hneg.trans
              ⟨fun hn => Or.inr ⟨hn, rfl⟩,
                fun h => (h.resolve_left (fun hc => Bool.noConfusion hc)).1⟩
        · rw [if_pos rfl, if_pos rfl]
          refine or_congr (and_congr htw₁ ?_) ?_
          · rw [Formula.realize_top]
            exact ⟨fun _ => ⟨rfl, fun _ => rfl⟩, fun _ => trivial⟩
          · rw [Formula.realize_bot]
            refine iff_of_false (fun h => h.2) ?_
            rintro ⟨-, hc | ⟨-, hc⟩⟩ <;> exact Bool.noConfusion hc
    exact key _ rfl rfl rfl rfl rfl rfl
  case tVer m f d =>
    have key : ∀ v : Fin 2 × Fin 3 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
        v (1, 0) = q.2 0 → v (1, 1) = q.2 1 → v (1, 2) = q.2 2 →
        (((oneHF (.qVer true d) (0, 0) q.1 ⊓ (if f then ⊤ else mLitF m)) ⊔
          (oneHF (.qVer false d) (0, 0) q.1 ⊓ (if f then ⊥ else ∼(mLitF m)))).Realize v ↔
          ((q = stHVer true d (w 0) ∧ (f = true ∨ MLit (w 0) (w 1) m)) ∨
            (q = stHVer false d (w 0) ∧ f = false ∧ ¬ MLit (w 0) (w 1) m))) := by
      intro v h0 h1 e0 e1 e2
      rw [Formula.realize_sup, Formula.realize_inf, Formula.realize_inf]
      have ho₁ : (oneHF (.qVer true d) (0, 0) q.1).Realize v ↔
          q = stHVer true d (w 0) := by
        refine (realize_oneHF e0 e1 e2).trans ?_
        simp only [h0]
        try exact Iff.rfl
      have ho₂ : (oneHF (.qVer false d) (0, 0) q.1).Realize v ↔
          q = stHVer false d (w 0) := by
        refine (realize_oneHF e0 e1 e2).trans ?_
        simp only [h0]
        try exact Iff.rfl
      cases f
      · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, Formula.realize_not]
        refine or_congr (and_congr ho₁ ?_) (and_congr ho₂ ?_)
        · exact (realize_mLitF h0 h1).trans
            ⟨fun h => Or.inr h, fun h => h.resolve_left (fun hc => Bool.noConfusion hc)⟩
        · exact (not_congr (realize_mLitF h0 h1)).trans
            ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
      · rw [if_pos rfl, if_pos rfl]
        refine or_congr (and_congr ho₁ ?_) ?_
        · rw [Formula.realize_top]
          exact ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
        · rw [Formula.realize_bot]
          exact iff_of_false (fun h => h.2) (fun h => Bool.noConfusion h.2.1)
    exact key _ rfl rfl rfl rfl rfl
  all_goals exact Iff.rfl

/-! ### The machines agree, and the reduction -/

/-- **The interpreted structure describes the unit-propagation machine.** -/
theorem agree_hornMachine :
    TMData.Agree (hornMapEquiv (A := A)) (hornMachine A)
      (tmData (hornTuringInterp.Map A)) where
  posn b := (relMap_posn b).symm
  le b b' := (relMap_le b b').symm
  tr b := (relMap_tr b).symm
  start b := (relMap_start b).symm
  acc b := (relMap_acc b).symm
  blank b := (relMap_blank b).symm
  right b := (relMap_right b).symm
  src b b' := (relMap_tsrc b b').symm
  read b b' := (relMap_tread b b').symm
  dst b b' := (relMap_tdst b b').symm
  write b b' := (relMap_twrite b b').symm
  inp b b' := (relMap_inp b b').symm

/-- **Correctness of the interpretation**: the interpreted structure is a
yes-instance of deterministic machine acceptance exactly when the CNF instance
is a yes-instance of HORN-SAT. Well-formedness and determinism hold
unconditionally – they were proved for every image, Horn or not – and
acceptance is `DescriptiveComplexity.hornMachine_accepts_iff`, transported along the
agreement. -/
theorem dtmAccept_map_iff_hornSatisfiable :
    DTMAccept (hornTuringInterp.Map A) ↔ HornSatisfiable A := by
  have hag := agree_hornMachine (A := A)
  constructor
  · rintro ⟨-, -, hacc⟩
    exact (hornMachine_accepts_iff (A := A)).mp (hag.accepts.mpr hacc)
  · intro hsat
    exact ⟨hag.wellFormed.mp hornMachine_wellFormed,
      hag.deterministic.mp hornMachine_deterministic,
      hag.accepts.mp ((hornMachine_accepts_iff (A := A)).mpr hsat)⟩

end Characterize

/-- **HORN-SAT reduces to deterministic machine acceptance**: the ordered
first-order reduction building the unit-propagation machine inside the
instance. -/
noncomputable def hornSat_ordered_fo_reduction_dtmAccept : HORNSAT ≤ᶠᵒ[≤] DTMAccept where
  Tag := UPTag
  dim := 3
  toInterpretation := hornTuringInterp
  correct _ _ _ _ _ := dtmAccept_map_iff_hornSatisfiable.symm

end HornTM

end DescriptiveComplexity
