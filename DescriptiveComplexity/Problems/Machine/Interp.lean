/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Machine.Defs
import DescriptiveComplexity.Problems.Machine.Hardness
import DescriptiveComplexity.OccurrenceFormulas
import DescriptiveComplexity.OrderWalk

/-!
# The transcription: `SAT ≤ᶠᵒ[≤] NTMAccept`

The first-order half of the reduction. The machine of a CNF formula was built
*semantically* in `DescriptiveComplexity.Problems.Machine.Hardness` – plain predicates
on tagged tuples, with its correctness `DescriptiveComplexity.satMachine_accepts_iff_satisfiable`
proved there. This file writes the defining formulas of an interpretation of
`Language.turing` in ordered CNF instances, shows each formula realizes exactly
the corresponding predicate of the machine, and bundles the result as the
ordered first-order reduction `DescriptiveComplexity.SatTM.sat_ordered_fo_reduction_ntmAccept`.

## Method

Everything is arranged so that no `simp` call ever faces a tag `match`:

* the binary symbols' formulas are written through two **shape helpers** –
  `cstF s` (“the second argument is the constant element pinned to the minima”)
  and `oneF s x` (“the second argument carries the tag `s` and the payload held
  by the variable `x`”) – matching the two shapes `DescriptiveComplexity.cst` and
  `DescriptiveComplexity.one` every state, symbol and transition of the machine has;
  each has one realization lemma, so each defining formula needs a `match` on
  its **first** tag only;
* realization lemmas take the valuation abstractly, with the values of the
  needed variables as equation hypotheses; at the call sites these are
  discharged by `rfl`, since the interpreted valuation reduces definitionally
  on concrete tags.

The transfer to `DescriptiveComplexity.NTMAccept` is then a fieldwise
`DescriptiveComplexity.TMData.Agree` along the identity equivalence: the machine the
interpreted structure describes agrees with `DescriptiveComplexity.satMachine`, so
acceptance and well-formedness transport, and correctness is inherited from the
semantic layer.
-/

namespace DescriptiveComplexity

open FirstOrder

namespace SatTM

open Language Structure SatOcc

/-! ### Formulas for the clause order -/

section Builders

variable {α : Type}

/-- `c` is the lowest clause, as a formula. -/
noncomputable def minClF (c : α) : satOrd.Formula α :=
  clF c ⊓ Formula.iAlls Unit (clF (Sum.inr ()) ⟹ SatOcc.leF (Sum.inl c) (Sum.inr ()))

/-- `c` is the highest clause, as a formula. -/
noncomputable def maxClF (c : α) : satOrd.Formula α :=
  clF c ⊓ Formula.iAlls Unit (clF (Sum.inr ()) ⟹ SatOcc.leF (Sum.inr ()) (Sum.inl c))

/-- `c'` is the clause immediately above `c`, as a formula. -/
noncomputable def nextClF (c c' : α) : satOrd.Formula α :=
  clF c ⊓ clF c' ⊓ SatOcc.ltF c c' ⊓
    Formula.iAlls Unit ((clF (Sum.inr ()) ⊓ SatOcc.ltF (Sum.inl c) (Sum.inr ())) ⟹
      SatOcc.leF (Sum.inl c') (Sum.inr ()))

/-- There is no clause at all, as a formula. -/
noncomputable def noClF : satOrd.Formula α :=
  Formula.iAlls Unit (∼(clF (Sum.inr () : α ⊕ Unit)))

end Builders

section BuilderRealize

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {α : Type} {v : α → A}

theorem realize_minClF {x : α} {c : A} (h : v x = c) :
    (minClF x).Realize v ↔ SatMinCl c := by
  simp only [minClF, Formula.realize_inf, realize_clF, Formula.realize_iAlls,
    Formula.realize_imp, SatOcc.realize_leF, Sum.elim_inl, Sum.elim_inr, h, SatMinCl]
  exact and_congr Iff.rfl ⟨fun hh e he => hh (fun _ => e) he, fun hh i hi => hh (i ()) hi⟩

theorem realize_maxClF {x : α} {c : A} (h : v x = c) :
    (maxClF x).Realize v ↔ SatMaxCl c := by
  simp only [maxClF, Formula.realize_inf, realize_clF, Formula.realize_iAlls,
    Formula.realize_imp, SatOcc.realize_leF, Sum.elim_inl, Sum.elim_inr, h, SatMaxCl]
  exact and_congr Iff.rfl ⟨fun hh e he => hh (fun _ => e) he, fun hh i hi => hh (i ()) hi⟩

theorem realize_nextClF {x y : α} {c c' : A} (hx : v x = c) (hy : v y = c') :
    (nextClF x y).Realize v ↔ SatNextCl c c' := by
  simp only [nextClF, Formula.realize_inf, realize_clF, SatOcc.realize_ltF,
    Formula.realize_iAlls, Formula.realize_imp, SatOcc.realize_leF, Sum.elim_inl,
    Sum.elim_inr, hx, hy, SatNextCl]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, fun e he hce => h4 (fun _ => e) ⟨he, hce⟩⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, fun i hi => h4 (i ()) hi.1 hi.2⟩

theorem realize_noClF : (noClF (α := α)).Realize v ↔ ∀ e : A, ¬ SatCl e := by
  simp only [noClF, Formula.realize_iAlls, Formula.realize_not, realize_clF, Sum.elim_inr]
  exact ⟨fun h e => h fun _ => e, fun h i => h (i ())⟩

end BuilderRealize

/-! ### The two shapes of the machine's elements, as formulas -/

section Shapes

/-- The second argument of a binary symbol is the constant element `cst s`:
its tag is `s` – checked statically – and its payload is the pair of minima. -/
noncomputable def cstF (s t' : SatTag) : satOrd.Formula (Fin 2 × Fin 2) :=
  if t' = s then minF (1, 0) ⊓ minF (1, 1) else ⊥

/-- The second argument of a binary symbol is `one s (v x)`: its tag is `s`,
its payload carries the value of the variable `x` and the minimum. -/
noncomputable def oneF (s : SatTag) (x : Fin 2 × Fin 2) (t' : SatTag) :
    satOrd.Formula (Fin 2 × Fin 2) :=
  if t' = s then eqF (1, 0) x ⊓ minF (1, 1) else ⊥

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
variable {v : Fin 2 × Fin 2 → A}

theorem realize_cstF {s : SatTag} {q : SatV A}
    (h0 : v (1, 0) = q.2 0) (h1 : v (1, 1) = q.2 1) :
    (cstF s q.1).Realize v ↔ q = cst s := by
  rw [cstF]
  by_cases hs : q.1 = s
  · rw [if_pos hs]
    simp only [Formula.realize_inf, realize_minF, h0, h1]
    constructor
    · rintro ⟨ha, hb⟩
      exact satV_ext hs (le_antisymm (ha botA) (botA_le _)) (le_antisymm (hb botA) (botA_le _))
    · rintro rfl
      exact ⟨fun a => botA_le a, fun a => botA_le a⟩
  · rw [if_neg hs]
    simp only [Formula.realize_bot, false_iff]
    exact fun hq => hs (congrArg Prod.fst hq)

theorem realize_oneF {s : SatTag} {x : Fin 2 × Fin 2} {q : SatV A}
    (h0 : v (1, 0) = q.2 0) (h1 : v (1, 1) = q.2 1) :
    (oneF s x q.1).Realize v ↔ q = one s (v x) := by
  rw [oneF]
  by_cases hs : q.1 = s
  · rw [if_pos hs]
    simp only [Formula.realize_inf, SatOcc.realize_eqF, realize_minF, h0, h1]
    constructor
    · rintro ⟨ha, hb⟩
      exact satV_ext hs ha (le_antisymm (hb botA) (botA_le _))
    · rintro rfl
      exact ⟨rfl, fun a => botA_le a⟩
  · rw [if_neg hs]
    simp only [Formula.realize_bot, false_iff]
    exact fun hq => hs (congrArg Prod.fst hq)

end Shapes

/-! ### The defining formulas -/

/-- The literal test on the source structure, for the statically known truth
value `v`: this is where the transition relation reads the input formula. -/
noncomputable def chkLitF (b : Bool) : satOrd.Formula (Fin 2 × Fin 2) :=
  if b then SatOcc.posF (0, 0) (0, 1) else SatOcc.negF (0, 0) (0, 1)

/-- Defining formula for `posn`. -/
noncomputable def posnF : SatTag → satOrd.Formula (Fin 1 × Fin 2)
  | .pStart => minF (0, 0) ⊓ minF (0, 1)
  | .pCell => minF (0, 1)
  | .pEnd => minF (0, 0) ⊓ minF (0, 1)
  | .pFill _ => ⊤
  | _ => ⊥

/-- Defining formula for `tr`: the payload promises of
`DescriptiveComplexity.SatTr`. -/
noncomputable def trF : SatTag → satOrd.Formula (Fin 1 × Fin 2)
  | .tGuessStart => minF (0, 0) ⊓ minF (0, 1)
  | .tGuessVal _ => minF (0, 1)
  | .tGuessEndAcc => minF (0, 0) ⊓ minF (0, 1) ⊓ noClF
  | .tGuessEndChk => minF (0, 1) ⊓ minClF (0, 0)
  | .tChk _ _ _ => clF (0, 0)
  | .tTurnNext _ => nextClF (0, 0) (0, 1)
  | .tTurnAcc _ => minF (0, 1) ⊓ maxClF (0, 0)
  | _ => ⊥

/-- Defining formula for `start`. -/
noncomputable def startF : SatTag → satOrd.Formula (Fin 1 × Fin 2)
  | .qGuess => minF (0, 0) ⊓ minF (0, 1)
  | _ => ⊥

/-- Defining formula for `acc`: any payload – acceptance is read off the tag
alone, exactly as `DescriptiveComplexity.SatAcc` does. -/
noncomputable def accF : SatTag → satOrd.Formula (Fin 1 × Fin 2)
  | .qAcc => ⊤
  | _ => ⊥

/-- Defining formula for `blank`. -/
noncomputable def blankF : SatTag → satOrd.Formula (Fin 1 × Fin 2)
  | .sBlank => minF (0, 0) ⊓ minF (0, 1)
  | _ => ⊥

/-- Defining formula for `right`: a static condition on the tag. -/
noncomputable def rightF : SatTag → satOrd.Formula (Fin 1 × Fin 2)
  | .tGuessStart => ⊤
  | .tGuessVal _ => ⊤
  | .tChk _ _ d => if d then ⊤ else ⊥
  | .tTurnNext d => if d then ⊥ else ⊤
  | .tTurnAcc d => if d then ⊥ else ⊤
  | _ => ⊥

/-- Defining formula for `inp`, the initial tape. -/
noncomputable def inpF : SatTag → SatTag → satOrd.Formula (Fin 2 × Fin 2)
  | .pStart, t' => cstF .sStart t'
  | .pCell, t' => oneF .sU (0, 0) t'
  | .pEnd, t' => cstF .sEnd t'
  | _, _ => ⊥

/-- Defining formula for `tsrc`. -/
noncomputable def tsrcF : SatTag → SatTag → satOrd.Formula (Fin 2 × Fin 2)
  | .tGuessStart, t' => cstF .qGuess t'
  | .tGuessVal _, t' => cstF .qGuess t'
  | .tGuessEndAcc, t' => cstF .qGuess t'
  | .tGuessEndChk, t' => cstF .qGuess t'
  | .tChk _ f d, t' => oneF (.qChk f d) (0, 0) t'
  | .tTurnNext d, t' => oneF (.qChk true d) (0, 0) t'
  | .tTurnAcc d, t' => oneF (.qChk true d) (0, 0) t'
  | _, _ => ⊥

/-- Defining formula for `tread`. -/
noncomputable def treadF : SatTag → SatTag → satOrd.Formula (Fin 2 × Fin 2)
  | .tGuessStart, t' => cstF .sStart t'
  | .tGuessVal _, t' => oneF .sU (0, 0) t'
  | .tGuessEndAcc, t' => cstF .sEnd t'
  | .tGuessEndChk, t' => cstF .sEnd t'
  | .tChk b _ _, t' => oneF (if b then .sT else .sF) (0, 1) t'
  | .tTurnNext d, t' => cstF (if d then .sEnd else .sStart) t'
  | .tTurnAcc d, t' => cstF (if d then .sEnd else .sStart) t'
  | _, _ => ⊥

/-- Defining formula for `tdst`: the one place the instance is consulted, in
the check clause, through `DescriptiveComplexity.SatTM.chkLitF`. -/
noncomputable def tdstF : SatTag → SatTag → satOrd.Formula (Fin 2 × Fin 2)
  | .tGuessStart, t' => cstF .qGuess t'
  | .tGuessVal _, t' => cstF .qGuess t'
  | .tGuessEndAcc, t' => cstF .qAcc t'
  | .tGuessEndChk, t' => oneF (.qChk false false) (0, 0) t'
  | .tChk b f d, t' =>
      (oneF (.qChk true d) (0, 0) t' ⊓ (if f then ⊤ else chkLitF b)) ⊔
        (oneF (.qChk false d) (0, 0) t' ⊓ (if f then ⊥ else ∼(chkLitF b)))
  | .tTurnNext d, t' => oneF (.qChk false (!d)) (0, 1) t'
  | .tTurnAcc _, t' => cstF .qAcc t'
  | _, _ => ⊥

/-- Defining formula for `twrite`. -/
noncomputable def twriteF : SatTag → SatTag → satOrd.Formula (Fin 2 × Fin 2)
  | .tGuessStart, t' => cstF .sStart t'
  | .tGuessVal b, t' => oneF (if b then .sT else .sF) (0, 0) t'
  | .tGuessEndAcc, t' => cstF .sEnd t'
  | .tGuessEndChk, t' => cstF .sEnd t'
  | .tChk b _ _, t' => oneF (if b then .sT else .sF) (0, 1) t'
  | .tTurnNext d, t' => cstF (if d then .sEnd else .sStart) t'
  | .tTurnAcc d, t' => cstF (if d then .sEnd else .sStart) t'
  | _, _ => ⊥

/-- **The interpretation of machine instances in ordered CNF instances.** The
order is `DescriptiveComplexity.lexLeF`, so its linearity comes from
`DescriptiveComplexity.tagTupleOrder` with no tag-pair analysis; every other symbol
matches on its first tag only, the shape of the second being delegated to
`DescriptiveComplexity.SatTM.cstF` and `DescriptiveComplexity.SatTM.oneF`. -/
noncomputable def satTuringInterp : FOInterpretation satOrd Language.turing SatTag 2 where
  relFormula {n} R :=
    match n, R with
    | _, .posn => fun t => posnF (t 0)
    | _, .tr => fun t => trF (t 0)
    | _, .start => fun t => startF (t 0)
    | _, .acc => fun t => accF (t 0)
    | _, .blank => fun t => blankF (t 0)
    | _, .right => fun t => rightF (t 0)
    | _, .le => fun t => lexLeF Language.sat 2 (t 0) (t 1)
    | _, .tsrc => fun t => tsrcF (t 0) (t 1)
    | _, .tread => fun t => treadF (t 0) (t 1)
    | _, .tdst => fun t => tdstF (t 0) (t 1)
    | _, .twrite => fun t => twriteF (t 0) (t 1)
    | _, .inp => fun t => inpF (t 0) (t 1)

/-! ### The realization lemmas

One per symbol of `Language.turing`, each saying its defining formula defines
the corresponding predicate of `DescriptiveComplexity.satMachine`. The universe of the
interpreted structure is definitionally `DescriptiveComplexity.SatV A`;
`DescriptiveComplexity.SatTM.satMapEquiv` names the identity equivalence, along which
the machines will be shown to agree. -/

section Characterize

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- The identity equivalence between the tagged tuples and the interpreted
universe. -/
def satMapEquiv : SatV A ≃ satTuringInterp.Map A := Equiv.refl (SatV A)

omit [Finite A] [Nonempty A] in
theorem relMap_posn (p : SatV A) : TMPosn (satMapEquiv p) ↔ SatPosn p := by
  rw [TMPosn, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  have hmin : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
      ((minF (0, 0) ⊓ minF (0, 1) : satOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
        ∀ a : A, w 0 ≤ a ∧ w 1 ≤ a) := by
    intro v h0 h1
    simp only [Formula.realize_inf, realize_minF, h0, h1, forall_and]
  cases t
  case pStart => exact hmin _ rfl rfl
  case pCell =>
    exact (realize_minF (L := Language.sat) (A := A) ((0 : Fin 1), (1 : Fin 2)))
  case pEnd => exact hmin _ rfl rfl
  case pFill _ =>
    exact iff_of_true (Formula.realize_top.mpr trivial) trivial
  all_goals exact Iff.rfl

omit [Finite A] [Nonempty A] in
theorem relMap_tr (p : SatV A) : TMTr (satMapEquiv p) ↔ SatTr p := by
  rw [TMTr, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  have hmin : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
      ((minF (0, 0) ⊓ minF (0, 1) : satOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
        IsMinTup w) := by
    intro v h0 h1
    simp only [Formula.realize_inf, realize_minF, h0, h1, IsMinTup]
  cases t
  case tGuessStart => exact hmin _ rfl rfl
  case tGuessVal _ =>
    exact (realize_minF (L := Language.sat) (A := A) ((0 : Fin 1), (1 : Fin 2)))
  case tGuessEndAcc =>
    have key : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
        ((minF (0, 0) ⊓ minF (0, 1) ⊓ noClF : satOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
          (IsMinTup w ∧ ∀ e : A, ¬ SatCl e)) := by
      intro v h0 h1
      simp only [Formula.realize_inf, realize_minF, realize_noClF, h0, h1, IsMinTup, and_assoc]
    exact key _ rfl rfl
  case tGuessEndChk =>
    have key : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
        ((minF (0, 1) ⊓ minClF (0, 0) : satOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
          ((∀ a : A, w 1 ≤ a) ∧ SatMinCl (w 0))) := by
      intro v h0 h1
      simp only [Formula.realize_inf, realize_minF, realize_minClF h0, h1]
    exact key _ rfl rfl
  case tChk b f d =>
    exact realize_clF.trans Iff.rfl
  case tTurnNext _ => exact realize_nextClF rfl rfl
  case tTurnAcc _ =>
    have key : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
        ((minF (0, 1) ⊓ maxClF (0, 0) : satOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
          ((∀ a : A, w 1 ≤ a) ∧ SatMaxCl (w 0))) := by
      intro v h0 h1
      simp only [Formula.realize_inf, realize_minF, realize_maxClF h0, h1]
    exact key _ rfl rfl
  all_goals exact Iff.rfl

omit [Finite A] [Nonempty A] in
theorem relMap_start (p : SatV A) : TMStart (satMapEquiv p) ↔ SatStart p := by
  rw [TMStart, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  have hmin : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
      ((minF (0, 0) ⊓ minF (0, 1) : satOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
        IsMinTup w) := by
    intro v h0 h1
    simp only [Formula.realize_inf, realize_minF, h0, h1, IsMinTup]
  cases t
  case qGuess => exact (hmin _ rfl rfl).trans ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  all_goals exact iff_of_false (by exact fun h => h) (fun h => SatTag.noConfusion h.1)

omit [Finite A] [Nonempty A] in
theorem relMap_acc (p : SatV A) : TMAcc (satMapEquiv p) ↔ SatAcc p := by
  rw [TMAcc, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case qAcc => exact iff_of_true (Formula.realize_top.mpr trivial) rfl
  all_goals exact iff_of_false (by exact fun h => h) (fun h => SatTag.noConfusion h)

omit [Finite A] [Nonempty A] in
theorem relMap_blank (p : SatV A) : TMBlank (satMapEquiv p) ↔ SatBlank p := by
  rw [TMBlank, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  have hmin : ∀ v : Fin 1 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
      ((minF (0, 0) ⊓ minF (0, 1) : satOrd.Formula (Fin 1 × Fin 2)).Realize v ↔
        IsMinTup w) := by
    intro v h0 h1
    simp only [Formula.realize_inf, realize_minF, h0, h1, IsMinTup]
  cases t
  case sBlank => exact (hmin _ rfl rfl).trans ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  all_goals exact iff_of_false (by exact fun h => h) (fun h => SatTag.noConfusion h.1)

omit [Finite A] [Nonempty A] in
theorem relMap_right (p : SatV A) : TMRight (satMapEquiv p) ↔ SatRight p := by
  rw [TMRight, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case tGuessStart => exact iff_of_true (Formula.realize_top.mpr trivial) trivial
  case tGuessVal _ => exact iff_of_true (Formula.realize_top.mpr trivial) trivial
  case tChk b f d =>
    cases d
    · exact iff_of_false (by exact fun h => h) (fun h => Bool.noConfusion h)
    · exact iff_of_true (Formula.realize_top.mpr trivial) rfl
  case tTurnNext d =>
    cases d
    · exact iff_of_true (Formula.realize_top.mpr trivial) rfl
    · exact iff_of_false (by exact fun h => h) (fun h => Bool.noConfusion h)
  case tTurnAcc d =>
    cases d
    · exact iff_of_true (Formula.realize_top.mpr trivial) rfl
    · exact iff_of_false (by exact fun h => h) (fun h => Bool.noConfusion h)
  all_goals exact Iff.rfl

omit [Finite A] [Nonempty A] in
theorem relMap_le (p q : SatV A) :
    TMLe (satMapEquiv p) (satMapEquiv q) ↔ tagTupleLe p q := by
  rw [TMLe, FOInterpretation.relMap_map]
  exact realize_lexLeF

omit [Language.sat.Structure A] in
/-- The three shapes of the initial tape, per tag of the cell. -/
theorem satInp_pStart_iff {w : Fin 2 → A} {a : SatV A} :
    SatInp ((SatTag.pStart, w) : SatV A) a ↔ a = symStart := by
  constructor
  · rintro (⟨-, h1, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact Prod.ext h1 (isMinTup_unique h2 isMinTup_bot)
    · exact SatTag.noConfusion h
    · exact SatTag.noConfusion h
  · rintro rfl
    exact Or.inl ⟨rfl, rfl, isMinTup_bot⟩

omit [Language.sat.Structure A] in
theorem satInp_pCell_iff {w : Fin 2 → A} {a : SatV A} :
    SatInp ((SatTag.pCell, w) : SatV A) a ↔ a = one .sU (w 0) := by
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h1, h2, h3⟩ | ⟨h, -⟩)
    · exact SatTag.noConfusion h
    · exact satV_ext h1 h2 (le_antisymm (h3 botA) (botA_le _))
    · exact SatTag.noConfusion h
  · rintro rfl
    exact Or.inr (Or.inl ⟨rfl, rfl, rfl, fun b => botA_le b⟩)

omit [Language.sat.Structure A] in
theorem satInp_pEnd_iff {w : Fin 2 → A} {a : SatV A} :
    SatInp ((SatTag.pEnd, w) : SatV A) a ↔ a = symEnd := by
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h1, h2⟩)
    · exact SatTag.noConfusion h
    · exact SatTag.noConfusion h
    · exact Prod.ext h1 (isMinTup_unique h2 isMinTup_bot)
  · rintro rfl
    exact Or.inr (Or.inr ⟨rfl, rfl, isMinTup_bot⟩)

theorem relMap_inp (p q : SatV A) :
    TMInp (satMapEquiv p) (satMapEquiv q) ↔ SatInp p q := by
  rw [TMInp, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case pStart => exact (realize_cstF rfl rfl).trans satInp_pStart_iff.symm
  case pCell => exact (realize_oneF rfl rfl).trans satInp_pCell_iff.symm
  case pEnd => exact (realize_cstF rfl rfl).trans satInp_pEnd_iff.symm
  all_goals
    refine iff_of_false (by exact fun h => h) ?_
    rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact SatTag.noConfusion h

theorem relMap_tsrc (p q : SatV A) :
    TMSrc (satMapEquiv p) (satMapEquiv q) ↔ SatSrc p q := by
  rw [TMSrc, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case tGuessStart => exact realize_cstF rfl rfl
  case tGuessVal _ => exact realize_cstF rfl rfl
  case tGuessEndAcc => exact realize_cstF rfl rfl
  case tGuessEndChk => exact realize_cstF rfl rfl
  case tChk b f d => exact realize_oneF rfl rfl
  case tTurnNext d => exact realize_oneF rfl rfl
  case tTurnAcc d => exact realize_oneF rfl rfl
  all_goals exact Iff.rfl

theorem relMap_tread (p q : SatV A) :
    TMRead (satMapEquiv p) (satMapEquiv q) ↔ SatRead p q := by
  rw [TMRead, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case tGuessStart => exact realize_cstF rfl rfl
  case tGuessVal _ => exact realize_oneF rfl rfl
  case tGuessEndAcc => exact realize_cstF rfl rfl
  case tGuessEndChk => exact realize_cstF rfl rfl
  case tChk b f d => exact realize_oneF rfl rfl
  case tTurnNext d => cases d <;> exact realize_cstF rfl rfl
  case tTurnAcc d => cases d <;> exact realize_cstF rfl rfl
  all_goals exact Iff.rfl

theorem relMap_twrite (p q : SatV A) :
    TMWrite (satMapEquiv p) (satMapEquiv q) ↔ SatWrite p q := by
  rw [TMWrite, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case tGuessStart => exact realize_cstF rfl rfl
  case tGuessVal b => exact realize_oneF rfl rfl
  case tGuessEndAcc => exact realize_cstF rfl rfl
  case tGuessEndChk => exact realize_cstF rfl rfl
  case tChk b f d => exact realize_oneF rfl rfl
  case tTurnNext d => cases d <;> exact realize_cstF rfl rfl
  case tTurnAcc d => cases d <;> exact realize_cstF rfl rfl
  all_goals exact Iff.rfl

omit [Finite A] [Nonempty A] in
/-- The check clause's new flag, realized: the literal test on the source. -/
theorem realize_chkLitF {b : Bool} {c x : A} {v : Fin 2 × Fin 2 → A}
    (h0 : v (0, 0) = c) (h1 : v (0, 1) = x) :
    (chkLitF b).Realize v ↔ SatLit c x b := by
  cases b
  · rw [chkLitF, if_neg (Bool.false_ne_true)]
    simp only [SatOcc.realize_negF, h0, h1, SatLit, SatPos, SatNeg, SatOcc.NegIn]
    simp
  · rw [chkLitF, if_pos rfl]
    simp only [SatOcc.realize_posF, h0, h1, SatLit, SatPos, SatNeg, SatOcc.PosIn]
    simp

theorem relMap_tdst (p q : SatV A) :
    TMDst (satMapEquiv p) (satMapEquiv q) ↔ SatDst p q := by
  rw [TMDst, FOInterpretation.relMap_map]
  obtain ⟨t, w⟩ := p
  cases t
  case tGuessStart => exact realize_cstF rfl rfl
  case tGuessVal _ => exact realize_cstF rfl rfl
  case tGuessEndAcc => exact realize_cstF rfl rfl
  case tGuessEndChk => exact realize_oneF rfl rfl
  case tTurnNext d => exact realize_oneF rfl rfl
  case tTurnAcc _ => exact realize_cstF rfl rfl
  case tChk b f d =>
    have key : ∀ v : Fin 2 × Fin 2 → A, v (0, 0) = w 0 → v (0, 1) = w 1 →
        v (1, 0) = q.2 0 → v (1, 1) = q.2 1 →
        (((oneF (.qChk true d) (0, 0) q.1 ⊓ (if f then ⊤ else chkLitF b)) ⊔
          (oneF (.qChk false d) (0, 0) q.1 ⊓
            (if f then ⊥ else ∼(chkLitF b)))).Realize v ↔
          ((q = stChk true d (w 0) ∧ (f = true ∨ SatLit (w 0) (w 1) b)) ∨
            (q = stChk false d (w 0) ∧ f = false ∧ ¬ SatLit (w 0) (w 1) b))) := by
      intro v h0 h1 h2 h3
      rw [Formula.realize_sup, Formula.realize_inf, Formula.realize_inf]
      refine or_congr (and_congr ((realize_oneF h2 h3).trans (by rw [h0])) ?_)
        (and_congr ((realize_oneF h2 h3).trans (by rw [h0])) ?_)
      · cases f
        · exact (realize_chkLitF h0 h1).trans
            ⟨fun h => Or.inr h, fun h => h.resolve_left (fun hc => Bool.noConfusion hc)⟩
        · exact iff_of_true (Formula.realize_top.mpr trivial) (Or.inl rfl)
      · cases f
        · rw [if_neg Bool.false_ne_true, Formula.realize_not]
          exact ⟨fun h => ⟨rfl, fun hl => h ((realize_chkLitF h0 h1).mpr hl)⟩,
            fun h hl => h.2 ((realize_chkLitF h0 h1).mp hl)⟩
        · exact iff_of_false (by exact fun h => h) (fun h => Bool.noConfusion h.1)
    exact key _ rfl rfl rfl rfl
  all_goals exact Iff.rfl

/-! ### The machines agree, and the reduction -/

/-- **The interpreted structure describes the machine of the instance**: every
field of `DescriptiveComplexity.tmData` on the interpreted structure agrees, along the
identity equivalence, with `DescriptiveComplexity.satMachine`. -/
theorem agree_satMachine :
    TMData.Agree (satMapEquiv (A := A)) (satMachine A)
      (tmData (satTuringInterp.Map A)) where
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
yes-instance of machine acceptance exactly when the CNF instance is
satisfiable. Well-formedness holds unconditionally
(`DescriptiveComplexity.satMachine_wellFormed`), and acceptance is
`DescriptiveComplexity.satMachine_accepts_iff_satisfiable`, both transported along the
agreement. -/
theorem ntmAccept_map_iff_satisfiable :
    NTMAccept (satTuringInterp.Map A) ↔ Satisfiable A := by
  have hag := agree_satMachine (A := A)
  constructor
  · rintro ⟨-, hacc⟩
    exact satMachine_accepts_iff_satisfiable.mp (hag.accepts.mpr hacc)
  · intro hsat
    exact ⟨hag.wellFormed.mp satMachine_wellFormed,
      hag.accepts.mp (satMachine_accepts_iff_satisfiable.mpr hsat)⟩

end Characterize

/-- **SAT reduces to acceptance by a nondeterministic machine**: the ordered
first-order reduction building `M_φ` inside the instance. -/
noncomputable def sat_ordered_fo_reduction_ntmAccept : SAT ≤ᶠᵒ[≤] NTMAccept where
  Tag := SatTag
  dim := 2
  toInterpretation := satTuringInterp
  correct _ _ _ _ _ := ntmAccept_map_iff_satisfiable.symm

end SatTM

end DescriptiveComplexity
