/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.DrawIxVar
import DescriptiveComplexity.Problems.Wide.DrawInstEval

/-!
# The spine's legs at an arbitrary file

`DescriptiveComplexity.Problems.Wide.DrawInstEval` read at a coarse file: one
variable's machinery per spine position, the legs' controls and states, and the
legs' runs with their costs.

The legs are generic in the **outer phase**: what they read of it is the
evaluation's own phases, embedded by `ep`, and the machineries' rules – never
the spine's, whose rule shape the space-bounded and the clocked programs do not
share. The fold of these legs is
`DescriptiveComplexity.Problems.Wide.NexSpine`.
-/

namespace DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

namespace Data

variable {L : Language.{0, 0}} (dt : Data L) {A R P : Type}
variable [Fintype dt.SlotIx]
variable [LinearOrder A] [LinearOrder R] [LinearOrder P]
-- The legs are generic in the outer phase: what they need of it is the
-- evaluation's own phases, embedded (`ep`) – the space-bounded program wraps
-- them in `OuterPh`, the clocked one in `NexPh`, and neither is read.
variable (ep : EvalPh dt.nv dt.PMF → P)
variable [Language.wide.Structure
  (Univ A R P dt.KIx dt.dd)]
variable [Finite A] [Finite R] [Finite P]
variable {PR : Prog A R P dt.CtlIx dt.SlotIx
  dt.KIx dt.dd}
variable {I : Type} [Finite I]
variable (F : LaidFile dt A R P I)
variable {elt : I → Univ A R P dt.KIx dt.dd}
variable (hinj : Function.Injective elt)
variable (hhasP : F.toLayout.HasName PR.zero)
variable (heltP : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  elt (F.toLayout.reg hhasP b c) = dt.blkElt b (pad PR.zero c))
variable (hsepP : F.toLayout.NameSep PR.zero dt.dd0Le) (hix : IsLinOrd F.le)
-- A register's block is the block of the element it stands for.
variable (hblkP : ∀ u : I, F.blk u = tagBlk (elt u).1)
variable {e₀ : Univ A R P dt.KIx dt.dd}
variable (he₀ : ∀ y, WMLe e₀ y)
-- The channel writes its marks in the tags' own order, the machine walks the
-- tape in the addresses'; the two agree.
variable (hord : ∀ x y : Univ A R P dt.KIx dt.dd,
  WMLe x y ↔ tagTupleLe x y)
variable [Nonempty A] [L.IsRelational] [L.Structure A]
variable [Finite dt.KIx]

section PostSt

variable (v : Univ A R P dt.KIx dt.dd → Prop)

open Classical in
/-- **The tape state after one spine position**: the round state at the
final VAL content, the variable's `new` track set at the marker to the
machinery's verdict. -/
noncomputable def ixPostVarSt
    (st : TapeSt dt A R P I)
    (m : I → Prop)
    (i : dt.d.B.ι) (b : Prop) :
    TapeSt dt A R P I :=
  { st with
    val := m
    new := fun i' r => if i' = i ∧ r = v then b else st.new i' r }

variable {zero one : A}
variable {st : TapeSt dt A R P I}
variable {m : I → Prop}
variable {i : dt.d.B.ι} {b : Prop}

omit [Fintype dt.SlotIx]
  [Finite A] [Finite R] [Finite P]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
/-- Off the marker, the post state's background is the round state's. -/
theorem ixBack_postVarSt_off
    (r : Univ A R P dt.KIx dt.dd → Prop)
    (hr : r ≠ v) :
    dt.ixBack F.toLayout zero one dt.dd0Le (dt.ixPostVarSt v st m i b) r =
      dt.ixBack F.toLayout zero one dt.dd0Le (dt.ixRoundSt st m) r := by
  classical
  funext s
  match s with
  | .new i' =>
    change bitVal zero one (if i' = i ∧ r = v then b else st.new i' r) = _
    rw [if_neg (fun h => hr h.2)]
    rfl
  | .reg | .regFirst | .regLast | .blk _ | .name _ | .pdd | .mir | .sav
  | .tgt | .val | .wk | .bot | .ltp | .old _ => rfl

omit [Fintype dt.SlotIx]
  [Finite A] [Finite R] [Finite P]
  [Nonempty A] [L.IsRelational] [L.Structure A] [Finite dt.KIx] in
omit [Finite I] in
/-- At the marker, the post state's background is the round state's with
the variable's stage slot updated to the verdict bit. -/
theorem ixBack_postVarSt_v :
    dt.ixBack F.toLayout zero one dt.dd0Le (dt.ixPostVarSt v st m i b) v =
      Function.update (dt.ixBack F.toLayout zero one dt.dd0Le (dt.ixRoundSt st m) v)
        (Slot.new i) (bitVal zero one b) := by
  classical
  funext s
  match s with
  | .new i' =>
    by_cases hi : i' = i
    · subst hi
      change bitVal zero one (if i' = i' ∧ v = v then b else st.new i' v) = _
      rw [if_pos ⟨rfl, rfl⟩, Function.update_self]
    · have hs : (Slot.new i' : dt.SlotIx) ≠ Slot.new i :=
        fun h => hi (by injection h)
      change bitVal zero one (if i' = i ∧ v = v then b else st.new i' v) = _
      rw [if_neg (fun h => hi h.1), Function.update_of_ne hs]
      rfl
  | .reg =>
    rw [Function.update_of_ne (show (Slot.reg : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .regFirst =>
    rw [Function.update_of_ne
      (show (Slot.regFirst : dt.SlotIx) ≠ Slot.new i from fun h => nomatch h)]
    rfl
  | .regLast =>
    rw [Function.update_of_ne
      (show (Slot.regLast : dt.SlotIx) ≠ Slot.new i from fun h => nomatch h)]
    rfl
  | .blk b' =>
    rw [Function.update_of_ne (show (Slot.blk b' : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .name j =>
    rw [Function.update_of_ne (show (Slot.name j : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .pdd =>
    rw [Function.update_of_ne (show (Slot.pdd : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .mir =>
    rw [Function.update_of_ne (show (Slot.mir : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .sav =>
    rw [Function.update_of_ne (show (Slot.sav : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .tgt =>
    rw [Function.update_of_ne (show (Slot.tgt : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .val =>
    rw [Function.update_of_ne (show (Slot.val : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .wk =>
    rw [Function.update_of_ne (show (Slot.wk : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .bot =>
    rw [Function.update_of_ne (show (Slot.bot : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .ltp =>
    rw [Function.update_of_ne (show (Slot.ltp : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl
  | .old i' =>
    rw [Function.update_of_ne (show (Slot.old i' : dt.SlotIx) ≠ Slot.new i from
      fun h => nomatch h)]
    rfl

end PostSt

/-! ### One position's leg -/

section Leg

variable {v v' : Univ A R P dt.KIx dt.dd → Prop}
-- The rule names of the machineries, one family per spine position and one for
-- the output: a leg reads no other site of the evaluation, so the *spine's*
-- rule-name type – which the clocked and the space-bounded programs do not
-- share – never appears here.
variable {rEmbM : ∀ (j : Fin dt.nv) (i : dt.VarSiteF (dt.varAt j)),
  dt.VarShF (dt.varAt j) i → R}
variable {rEmbO : ∀ i : dt.VarSiteF (none : dt.VarIx),
  dt.VarShF (none : dt.VarIx) i → R}
-- The accepting phase the output's machinery exits into: the caller's, since
-- it is the one phase of a leg that is not the evaluation's own.
variable (accPh : P)
-- What a leg asks of the program is its *machinery's* rules, not the whole
-- evaluation's: one copy of `varRuleF` per position, at the phases the
-- evaluation embeds. A spine supplies them by projecting its own rules.
variable (hrulesM : ∀ (j : Fin dt.nv) (i : dt.VarSiteF (dt.varAt j))
    (ρ : dt.VarShF (dt.varAt j) i),
  PR.rules (rEmbM j i ρ) =
    dt.varRuleF PR.zero PR.one (dt.varAt j)
      (dt.varArgsOf PR.zero PR.one (dt.varAt j))
      (fun p => ep (.sub (Sum.inl ⟨j, p⟩))) (ep (.chk j.succ)) i ρ)
variable (hrulesOut : ∀ (i : dt.VarSiteF (none : dt.VarIx))
    (ρ : dt.VarShF (none : dt.VarIx) i),
  PR.rules (rEmbO i ρ) =
    dt.varRuleF PR.zero PR.one none (dt.varArgsOf PR.zero PR.one none)
      (fun p => ep (.sub (Sum.inr p))) accPh i ρ)
variable (hR : PR.table.Reads)
variable (hlin : IsLinOrd
  (WMLe (A := Univ A R P dt.KIx dt.dd)))
variable {gtop gbot : I}
variable (htop : ∀ y, F.le y gtop) (hbot : ∀ y, F.le gbot y)
-- The program's working area lies below its file: an address missing the least
-- element is below every register. Free at the input channel's ladder
-- (`wmSetLt_wmSeg_of_not_bot`); a program that builds its own file arranges it
-- by choosing where to put it.
variable (hwork : ∀ {r : Univ A R P dt.KIx dt.dd → Prop},
  (∀ x, r x → ∃ i : dt.KIx, x.1 = Tag.arg i) →
  ∀ u : I, WMSetLt WMLe r (F.cell u))
variable (hv : WMSetLt WMLe v (F.cell gbot)) (hvi : WMIncr WMLe v v')
variable {Use : I → Prop}
variable (hmono : ∀ u u', WMLt F.le u u' ↔ WMLt WMLe (elt u) (elt u'))
variable (hup : ∀ (u : I) (x : Univ A R P dt.KIx dt.dd),
  Use u → WMLt WMLe (elt u) x → ∃ u', Use u' ∧ elt u' = x)
variable (hvh : IxHolds elt Use v)
variable (hxdUse : ∀ {iv : dt.d.B.ι} (ℓ : Fin (dt.d.B.arity iv))
  (b : Lex (Fin dt.dd0 → A)), Use (dt.ixStageXD F hhasP ℓ b))
-- The widths a clocked stage atom of any position's variable is priced at.
variable (w wG wP wR wK : ℕ)
variable (hgap : ∀ u u' : I, IxSucc F.le u u' →
  wideRank (F.cell u') - wideRank (F.cell u) ≤ wG)
variable (hwP : wideRank (F.cell gtop) + 2 +
  ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) + wideRank (F.cell gbot) ≤ wP)
-- The reset and the seek are charged against the working area, not the tape:
-- both run at the marker or at the built TARGET, which lie below the file.
variable (hwR : ∀ s : Univ A R P dt.KIx dt.dd → Prop,
  WMSetLt WMLe s (F.cell gbot) → wideRank s + 4 ≤ wR)
variable (hwK : ∀ T : Univ A R P dt.KIx dt.dd → Prop,
  WMSetLt WMLe T (F.cell gbot) →
  wideRank T *
      (1 + (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
          wideRank (F.cell gbot)) +
        (wideRank (F.cell gtop) + ((ixRank F.le gtop - ixRank F.le gbot) * wG + 1) +
          wideRank (F.cell gbot) + 4)) + 1 +
    (wideRank (F.cell gtop) + 3 + (ixRank F.le gtop - ixRank F.le gbot) * wG +
      wideRank (F.cell gbot)) ≤ wK)
-- Every named register of the file is within `w` of the marker: the width a
-- walk to a cell is charged, uniform over the blocks and the tuples.
variable (hcostR : ∀ (b : Fin dt.ko ⊕ Fin dt.ki) (c : Fin dt.dd0 → A),
  2 * (wideRank (F.cell (F.toLayout.reg hhasP b c)) - wideRank v) + 2 ≤ w)
variable {ιV : Type} [LinearOrder ιV] [Finite ιV] {a₀ aT : ιV}
variable (hbotV : ∀ a : ιV, a₀ ≤ a) (htopV : ∀ a : ιV, a ≤ aT)
variable (mV : ιV → I → Prop)
variable (hmV0 : mV a₀ = fun _ => False)
variable (hIncr : ∀ a a' : ιV, a < a' → (∀ b, ¬(a < b ∧ b < a')) →
  WMIncr F.le (mV a) (mV a'))
variable (hTestT : ∀ u : I, dt.InnerFull F.blk (mV aT) u)
variable (hTestF : ∀ a, a < aT → ∃ u : I, ¬dt.InnerFull F.blk (mV a) u)

/-- **The control after one position's leg**: the machinery's exit fold —
`DescriptiveComplexity.Draw.Data.ixVarMachine_run`'s final control, at the
position's variable. -/
noncomputable def ixLegCtl (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixRoundSt st (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j) (dt.ixRoundSt st (mV a))
          elt (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) : dt.CtlIx → A :=
  (dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
    (dt.ixRoundFX (elt := elt) F hinj hhasP heltP (dt.varAt j) st v mV semOf
      (dt.ixVarFM (elt := elt) F hinj hhasP heltP (dt.varAt j) st v mV semOf
        (dt.ixGatesFs F PR.zero PR.one hhasP (dt.varAt j) st v
          (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
          dt.card_le_ntgDim
          (fun t => le_trans (Finset.le_sup
            (f := fun t' : dt.X.Tag => (dt.domPk t').n)
            (Finset.mem_univ t)) dt.domDepth_le_eDim)
          (fun t => le_trans (Finset.le_sup
            (f := fun t' : dt.X.Tag =>
              (blkAtoms (dt.domPk t').mat).length)
            (Finset.mem_univ t)) dt.domReads_le_nfDim)
          tOf (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterBlockSt
          ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt f₀
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))
          (dt.arOf (dt.varAt j))) aT) aT)
    (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)) v)

/-- **The control after one position's leg, threaded** — the twin of
`DescriptiveComplexity.Draw.Data.ixLegCtl`, with the VAL loop's rounds run
at the states the thread produces for them. -/
noncomputable def ixLegCtlT (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (semT : ∀ (p : IxScratch dt A R P I)
      (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) : dt.CtlIx → A :=
  (dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
    (dt.ixVarFXT (elt := elt) F hinj hhasP heltP (dt.varAt j) st v mV semT
      (dt.ixVarFG (PR := PR) F hhasP (dt.varAt j) st v tOf f₀) aT)
    (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
      (dt.ixVarStE (elt := elt) F hinj hhasP heltP (dt.varAt j) st v mV semT
        (dt.ixVarFG (PR := PR) F hhasP (dt.varAt j) st v tOf f₀) aT) v)

/-- **The tape state after one position's leg, threaded**: the VAL loop's
exit state — the entry state's SAV and TARGET normalized if any of its
rounds ran a stage atom — with the variable's `new` track written at the
marker. -/
noncomputable def ixLegStT (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (semT : ∀ (p : IxScratch dt A R P I)
      (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) : TapeSt dt A R P I :=
  dt.ixPostVarSt v
    (dt.ixVarStE (elt := elt) F hinj hhasP heltP (dt.varAt j) st v mV semT
      (dt.ixVarFG (PR := PR) F hhasP (dt.varAt j) st v tOf f₀) aT)
    (mV aT) (dt.varList.get j)
    ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
      (dt.ixLegCtlT (elt := elt) (aT := aT) F hinj hhasP heltP mV j st tOf semT f₀))

include hord hinj hhasP heltP in
omit [Finite R] [Finite P] [Finite dt.KIx]
  [Finite ιV] in
omit [Finite I] hord in
/-- **What a leg leaves alone**: the machinery writes its own two scratch
registers and its stage bit, so the mirror, the marker, the bottom and end
marks and the stage dictionary all ride — which is what carries the next
position's pack and, one scale up, the sweep's own invariants. -/
theorem ixLegStT_fields (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (semT : ∀ (p : IxScratch dt A R P I)
      (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) :
    (dt.ixLegStT (elt := elt) (aT := aT) F hinj hhasP heltP mV j st tOf semT f₀).mir = st.mir ∧
      (dt.ixLegStT (elt := elt) (aT := aT) F hinj hhasP heltP mV j st tOf semT f₀).wk = st.wk ∧
      (dt.ixLegStT (elt := elt) (aT := aT) F hinj hhasP heltP mV j st tOf semT f₀).bot = st.bot ∧
      (dt.ixLegStT (elt := elt) (aT := aT) F hinj hhasP heltP mV j st tOf semT f₀).old = st.old ∧
      (dt.ixLegStT (elt := elt) (aT := aT) F hinj hhasP heltP mV j st tOf semT f₀).ltp = st.ltp ∧
      (dt.ixLegStT (elt := elt) (aT := aT) F hinj hhasP heltP mV j st tOf semT f₀).val = mV aT := by
  obtain ⟨hwk, hmir, hbot, -, hold⟩ := dt.ixRoundEndSt_fields (elt := elt)
    (zero := PR.zero) (one := PR.one) (hhas := hhasP) F (dt.varAt j)
    (dt.ixVarStT (elt := elt) F hinj hhasP heltP (dt.varAt j) st v mV semT
      (dt.ixVarFG (PR := PR) F hhasP (dt.varAt j) st v tOf f₀) aT) v
    (dt.ixVarFMT (elt := elt) F hinj hhasP heltP (dt.varAt j) st v mV semT
      (dt.ixVarFG (PR := PR) F hhasP (dt.varAt j) st v tOf f₀) aT)
  have hltp : (dt.ixVarStE (elt := elt) F hinj hhasP heltP (dt.varAt j) st v mV semT
      (dt.ixVarFG (PR := PR) F hhasP (dt.varAt j) st v tOf f₀) aT).ltp = st.ltp := by
    rw [ixVarStE, dt.ixRoundEndSt_eq (zero := PR.zero) (one := PR.one)]
    rfl
  exact ⟨hmir, hwk, hbot, hold, hltp, rfl⟩

/-- **What one leg of the evaluation's spine is charged**: the walk-back, the
whole machinery of the position's variable, and the written exit. Uniform over
the positions – the largest of the variables' costs – so the spine's fold is a
single width. -/
noncomputable def ixLegCost (dt : Data L) (A : Type) (w wP wR wK n : ℕ) : ℕ :=
  1 + (Finset.univ.sup fun j : Fin dt.nv =>
    dt.ixVarCost A (dt.varAt j) w wP wR wK n) + 1

/-- **What the output's leg is charged**: the same shape at the output's own
machinery, which is the `none` variable's. -/
noncomputable def ixOutLegCost (dt : Data L) (A : Type) (w wP wR wK n : ℕ) : ℕ :=
  1 + dt.ixVarCost A none w wP wR wK n + 1

/-! ### The costs, factored

The clock compares a *product*: a width and a number of rounds, each bounded on
its own (`nexTotal_lt_two_pow`). So each cost above, which is «once plus a
round's cost per VAL content», is rewritten here as «a width times the rounds
and one more» – the width is the sum of the two parts, and nothing about the
program is used but the shape of the definitions. -/

/-- **A variable's machinery, as one width**: what it pays once and what it pays
per VAL round, added. -/
noncomputable def ixVarCD (dt : Data L) (A : Type) (vi : dt.VarIx)
    (w wP wR wK : ℕ) : ℕ :=
  dt.ixVarGatesCost A vi w wP + dt.ixRoundCost A vi w wP wR wK + 3 * wP + 6 +
    (2 * wP + dt.ixRoundCost A vi w wP wR wK + 3)

/-- **The width of a leg of the spine**: the largest variable's, and the leg's
own two steps. -/
noncomputable def ixLegWidth (dt : Data L) (A : Type) (w wP wR wK : ℕ) : ℕ :=
  4 + Finset.univ.sup fun j : Fin dt.nv => dt.ixVarCD A (dt.varAt j) w wP wR wK

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A] [Finite R]
  [Finite P] [Finite I] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite dt.KIx] in
/-- **A variable's whole cost is its width times the rounds and one more.** -/
theorem ixVarCost_le_mul (vi : dt.VarIx) (w wP wR wK n : ℕ) :
    dt.ixVarCost A vi w wP wR wK n ≤ dt.ixVarCD A vi w wP wR wK * (n + 1) := by
  have hle : 2 * wP + dt.ixRoundCost A vi w wP wR wK + 3 ≤
      dt.ixVarCD A vi w wP wR wK := by
    simp only [ixVarCD]
    omega
  have hmul := Nat.mul_le_mul_right n hle
  rw [Nat.mul_succ]
  simp only [ixVarCost, ixVarCD] at *
  omega

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A] [Finite R]
  [Finite P] [Finite I] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite dt.KIx] in
/-- **A leg's whole cost, and its dispatch, is its width times the rounds and
one more.** -/
theorem ixLegCost_le_mul (w wP wR wK n : ℕ) :
    dt.ixLegCost A w wP wR wK n + 2 ≤ dt.ixLegWidth A w wP wR wK * (n + 1) := by
  classical
  have hsup : (Finset.univ.sup fun j : Fin dt.nv =>
        dt.ixVarCost A (dt.varAt j) w wP wR wK n) ≤
      (Finset.univ.sup fun j : Fin dt.nv => dt.ixVarCD A (dt.varAt j) w wP wR wK) *
        (n + 1) := by
    refine Finset.sup_le fun j _ =>
      le_trans (dt.ixVarCost_le_mul (A := A) (dt.varAt j) w wP wR wK n) ?_
    exact Nat.mul_le_mul_right _ (Finset.le_sup
      (f := fun j' : Fin dt.nv => dt.ixVarCD A (dt.varAt j') w wP wR wK)
      (Finset.mem_univ j))
  have hexp : dt.ixLegWidth A w wP wR wK * (n + 1) =
      4 * (n + 1) +
        (Finset.univ.sup fun j : Fin dt.nv => dt.ixVarCD A (dt.varAt j) w wP wR wK) *
          (n + 1) := by
    rw [ixLegWidth, Nat.add_mul]
  have hfour : (4 : ℕ) ≤ 4 * (n + 1) := by omega
  rw [ixLegCost, hexp]
  omega

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A] [Finite R]
  [Finite P] [Finite I] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite dt.KIx] in
/-- **The spine's whole cost, factored**: a width – the leg's, times the number
of positions – and the number of VAL rounds and one more. This is the shape the
clock compares (`nexTotal_lt_two_pow`), so what an instantiation owes is a bound
on each factor separately. -/
theorem ixSpineCost_le_mul (w wP wR wK n : ℕ) :
    (dt.ixLegCost A w wP wR wK n + 2) * dt.nv ≤
      (dt.ixLegWidth A w wP wR wK * dt.nv) * (n + 1) :=
  le_trans (Nat.mul_le_mul_right _ (dt.ixLegCost_le_mul (A := A) w wP wR wK n))
    (le_of_eq (Nat.mul_right_comm _ _ _))

/-- **The width of the whole clocked evaluation**: the spine's width times its
positions, the output machinery's own, and the four steps that join them – the
dispatch into the spine, the dispatch into the output's leg and the two the legs
themselves pay. This is the first factor the clock compares. -/
noncomputable def ixEvalWidth (dt : Data L) (A : Type) (w wP wR wK : ℕ) : ℕ :=
  dt.ixLegWidth A w wP wR wK * dt.nv + dt.ixVarCD A none w wP wR wK + 4

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A] [Finite R]
  [Finite P] [Finite I] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite dt.KIx] in
private theorem evalTotal_shape {S V B C n : ℕ} (h1 : S ≤ B * (n + 1))
    (h2 : V ≤ C * (n + 1)) :
    1 + S + 1 + (1 + V + 1) ≤ (B + C + 4) * (n + 1) := by
  have hexp : (B + C + 4) * (n + 1) =
      B * (n + 1) + C * (n + 1) + 4 * (n + 1) := by ring
  have h4 : 4 ≤ 4 * (n + 1) := Nat.le_mul_of_pos_right 4 (Nat.succ_pos n)
  omega

omit [Fintype dt.SlotIx] [LinearOrder A] [LinearOrder R] [LinearOrder P]
  [Language.wide.Structure (Univ A R P dt.KIx dt.dd)] [Finite A] [Finite R]
  [Finite P] [Finite I] [Nonempty A] [L.IsRelational] [L.Structure A]
  [Finite dt.KIx] in
/-- **The clocked evaluation's whole cost, factored**: one width times the VAL
rounds and one more. This is what
`DescriptiveComplexity.Draw.Data.nexProg_wideAccept_legs` asks of the
evaluation leg – the run's count is exactly the left-hand side. -/
theorem ixEvalCost_le_mul (w wP wR wK n : ℕ) :
    1 + (dt.ixLegCost A w wP wR wK n + 2) * dt.nv + 1 +
        dt.ixOutLegCost A w wP wR wK n ≤
      dt.ixEvalWidth A w wP wR wK * (n + 1) :=
  evalTotal_shape (dt.ixSpineCost_le_mul (A := A) w wP wR wK n)
    (dt.ixVarCost_le_mul (A := A) none w wP wR wK n)

include hrulesM hR hlin hix hsepP hhasP hinj heltP hord he₀ htop hbot hwork hv hvi
  hmono hup hvh hxdUse hgap hwP hwR hwK hcostR hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **One spine position's leg — threaded**: as
`DescriptiveComplexity.Draw.Data.ixVarLeg_run` without the boundary
hypotheses `hsav`/`htgt`, which the sweep cannot supply at more than one
address. The leg ends in
`DescriptiveComplexity.Draw.Data.ixLegStT`, the machinery's own exit state
with the stage bit written at the marker. -/
theorem ixVarLeg_run_thread_reachesIn (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (hwkSt : st.wk = fun r => r = v)
    (TestOf : Fin (dt.arOf (dt.varAt j)) → I → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (dt.varAt j))) (u : I),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
        (PR.passTracksAt F.cell Slot.mir (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
          st.mir (F.cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (hwitOf : ∀ (ℓ : Fin (dt.arOf (dt.varAt j))) (t' : dt.X.Tag),
      wmBlk (ixAddr elt st.mir)
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R P dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hmir : st.mir = ixMark elt v)
    (hbotSt : st.bot = fun r => r = (fun _ => False))
    (semT : ∀ (p : IxScratch dt A R P I)
      (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b))
    (hDom : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk (ixAddr elt st.mir)
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R P dt.KIx))))
    (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx
      dt.dd)).ReachesIn (dt.ixLegCost A w wP wR wK (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (ep (.sub (dt.smEntry j))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (ep (.chk j.succ))
          (dt.ixLegCtlT (elt := elt) (aT := aT) F hinj hhasP heltP
            mV j st tOf semT f₀)), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixLegStT (elt := elt) (aT := aT) F hinj hhasP heltP mV j st tOf semT f₀))
          (mV aT)) (PR.syElt PR.blank)⟩ := by
  classical
  set embJ : dt.VarPhF (dt.varAt j) → P :=
    fun p => ep (.sub (Sum.inl ⟨j, p⟩)) with hembJ
  have hrulesJ : ∀ (i : dt.VarSiteF (dt.varAt j))
      (ρ : dt.VarShF (dt.varAt j) i),
      PR.rules (rEmbM j i ρ) =
        dt.varRuleF PR.zero PR.one (dt.varAt j)
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)) embJ
          (ep (.chk j.succ)) i ρ :=
    fun i ρ => hrulesM j i ρ
  have hrulesV : ∀ (i : dt.VarSiteF (dt.varAt j))
      (ρ : dt.VarShF (dt.varAt j) i),
      PR.rules (rEmbM j i ρ) =
        dt.varRule PR.zero PR.one embJ
          (dt.gatesRule (one := PR.one) (v := dt.varAt j)
            (emb := fun p => embJ (.gatesP p))
            (argsG := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsG)
            (wellGOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).wellGOf)
            (setFail := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).setFail)
            (enterSt :=
              (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterBlockSt)
            (failPh := embJ .vchk1) (exitPh := embJ .vchk1))
          (dt.roundRule (one := PR.one) (emb := fun p => embJ (.matrixP p))
            (ruleG := dt.igatesRule (one := PR.one) (v := dt.varAt j)
              (emb := fun p => embJ (.matrixP (.igP p)))
              (argsG := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsIG)
              (wellGOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).wellIGOf)
              (setFailOf :=
                (dt.varArgsOf PR.zero PR.one (dt.varAt j)).setFailIGOf)
              (enterSt := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterIGSt)
              (exitPh := embJ (.matrixP .rchk)))
            (ruleX := dt.matrixRule (zero := PR.zero) (one := PR.one)
              (v := dt.varAt j)
              (emb := fun p => embJ (.matrixP (.matP p)))
              (argsA := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsA)
              (enterSt :=
                (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterAtomSt)
              (exitPh := embJ .mchk1))
            (pxEntry := embJ (.matrixP (.matP (.chk 0))))
            (exitPh := embJ .mchk1)
            (existFlag := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).existFlag)
            (allFlag := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).allFlag))
          (embJ (.gatesP (.chk 0))) (embJ (.matrixP (.igP (.chk 0))))
          (ep (.chk j.succ))
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).newSlot
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).gateFlag
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).initSt
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).storeCarry i ρ :=
    fun i ρ => hrulesM j i ρ
  -- the walk back to the marker
  have hback := dt.step_var_back F hrulesV hR hlin hvi
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (mval := st.val) (f := f₀)
    (by rw [ixBack_wk, hwkSt])
  -- the machinery, at the states its own thread produces
  have hmach := ixVarMachine_run_thread_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
    (hix := hix) (hinj := hinj) (heltP := heltP) (he₀ := he₀) (hord := hord)
    (vi := dt.varAt j) (st := st) (hrules := hrulesJ) (hR := hR) (hlin := hlin)
    (htop := htop) (hbot := hbot) (hwork := hwork) (hv := hv) (hvi := hvi)
    (hwkSt := hwkSt) (hmono := hmono) (hup := hup) (hvh := hvh)
    (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR) (hwK := hwK)
    (hcostR := hcostR) (TestOf := TestOf) (hcompatOf := hcompatOf)
    (tOf := tOf) (hbotV := hbotV) (htopV := htopV) (mV := mV) (hmV0 := hmV0)
    (hIncr := hIncr) (hTestT := hTestT) (hTestF := hTestF) (hmir := hmir)
    (hbotSt := hbotSt) (semT := semT) (hDom := hDom) (hwitOf := hwitOf)
    (hTestOf := hTestOf) (f₀ := f₀)
  -- the loop's exit state, and the register it holds
  set stE := dt.ixVarStE (elt := elt) F hinj hhasP heltP (dt.varAt j) st v mV semT
    (dt.ixVarFG (PR := PR) F hhasP (dt.varAt j) st v tOf f₀) aT with hstE
  have hvalE : stE.val = mV aT := by
    rw [hstE]; exact dt.ixVarStE_val (elt := elt) F hinj hhasP heltP (dt.varAt j) st mV semT _ aT
  have hwkE : stE.wk = fun r => r = v := by
    rw [hstE, ixVarStE]
    refine ((dt.ixRoundEndSt_fields (elt := elt) (zero := PR.zero)
      (one := PR.one) (hhas := hhasP) F (dt.varAt j) _ v _).1).trans ?_
    exact ((dt.ixVarStT_fields (elt := elt) F hinj hhasP heltP (dt.varAt j) st mV semT
      (dt.ixVarFG (PR := PR) F hhasP (dt.varAt j) st v tOf f₀) aT).1).trans hwkSt
  have hround : dt.ixRoundSt stE (mV aT) = stE := hvalE ▸ dt.ixRoundSt_val stE
  -- the written exit
  have hns : (dt.varArgsOf PR.zero PR.one (dt.varAt j)).newSlot ≠
      Slot.val := fun h => nomatch h
  have hexit := dt.step_var_exit F hrulesV hR hlin hix hbot hv hvi
    (f := dt.ixLegCtlT (elt := elt) (aT := aT) F hinj hhasP heltP mV j st tOf semT f₀)
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le stE)
    (rest' := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
      (dt.ixLegStT (elt := elt) (aT := aT) F hinj hhasP heltP mV j st tOf semT f₀))
    (mval := mV aT)
    (hvalE ▸ dt.ixVarBg_back F hix htop stE hwkE) hns
    (fun r hr => (dt.ixBack_postVarSt_off F v r hr).trans
      (congrArg (fun X => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le X r) hround))
    ((dt.ixBack_postVarSt_v (zero := PR.zero) (one := PR.one) F v).trans
      (congrArg (fun X => Function.update
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le X v) _ _) hround))
  refine TMData.ReachesIn.mono ?_
    (((TMData.reachesIn_of_step hback).trans hmach).tail hexit)
  simp only [ixLegCost]
  have hj : dt.ixVarCost A (dt.varAt j) w wP wR wK (Nat.card ιV) ≤
      Finset.univ.sup fun j' : Fin dt.nv =>
        dt.ixVarCost A (dt.varAt j') w wP wR wK (Nat.card ιV) :=
    Finset.le_sup (f := fun j' : Fin dt.nv =>
      dt.ixVarCost A (dt.varAt j') w wP wR wK (Nat.card ιV)) (Finset.mem_univ j)
  omega

include hrulesM hR hlin hix hsepP hhasP hinj heltP htop hbot hv hvi hgap hwP
  hcostR in
omit [LinearOrder ιV] [Finite ιV] in
/-- **One spine position's leg at a junk address**: the walk-back, the
machinery's failing gates, and the erased stage slot at the marker — the
verdict `False`, the VAL register untouched. -/
theorem ixVarLegFail_reachesIn (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (hwkSt : st.wk = fun r => r = v)
    (TestOf : Fin (dt.arOf (dt.varAt j)) → I → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (dt.varAt j))) (u : I),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
        (PR.passTracksAt F.cell Slot.mir (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
          st.mir (F.cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (htagOf : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      dt.dspTagOf PR.zero PR.one
        (wmBlk (ixAddr elt st.mir)
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            Tag R P dt.KIx)) = tOf ℓ)
    (ℓ₀ : Fin (dt.arOf (dt.varAt j)))
    (hTestLt : ∀ ℓ : Fin (dt.arOf (dt.varAt j)), (ℓ : ℕ) < (ℓ₀ : ℕ) →
      ∀ u, TestOf ℓ u)
    {u₀ : I}
    (hfail : ¬TestOf ℓ₀ u₀) (f₀ : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx
      dt.dd)).ReachesIn (dt.ixLegCost A w wP wR wK (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (ep (.sub (dt.smEntry j))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (ep (.chk j.succ))
          (dt.ixFailCtl (PR := PR) (v := v) F hhasP (dt.varAt j) st tOf ℓ₀
            ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt f₀
              (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixPostVarSt v st st.val (dt.varList.get j) False))
          st.val) (PR.syElt PR.blank)⟩ := by
  classical
  set embJ : dt.VarPhF (dt.varAt j) → P :=
    fun p => ep (.sub (Sum.inl ⟨j, p⟩)) with hembJ
  have hrulesJ : ∀ (i : dt.VarSiteF (dt.varAt j))
      (ρ : dt.VarShF (dt.varAt j) i),
      PR.rules (rEmbM j i ρ) =
        dt.varRuleF PR.zero PR.one (dt.varAt j)
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)) embJ
          (ep (.chk j.succ)) i ρ :=
    fun i ρ => hrulesM j i ρ
  have hrulesV : ∀ (i : dt.VarSiteF (dt.varAt j))
      (ρ : dt.VarShF (dt.varAt j) i),
      PR.rules (rEmbM j i ρ) =
        dt.varRule PR.zero PR.one embJ
          (dt.gatesRule (one := PR.one) (v := dt.varAt j)
            (emb := fun p => embJ (.gatesP p))
            (argsG := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsG)
            (wellGOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).wellGOf)
            (setFail := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).setFail)
            (enterSt :=
              (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterBlockSt)
            (failPh := embJ .vchk1) (exitPh := embJ .vchk1))
          (dt.roundRule (one := PR.one) (emb := fun p => embJ (.matrixP p))
            (ruleG := dt.igatesRule (one := PR.one) (v := dt.varAt j)
              (emb := fun p => embJ (.matrixP (.igP p)))
              (argsG := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsIG)
              (wellGOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).wellIGOf)
              (setFailOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).setFailIGOf)
              (enterSt := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterIGSt)
              (exitPh := embJ (.matrixP .rchk)))
            (ruleX := dt.matrixRule (zero := PR.zero) (one := PR.one)
              (v := dt.varAt j)
              (emb := fun p => embJ (.matrixP (.matP p)))
              (argsA := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsA)
              (enterSt := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterAtomSt)
              (exitPh := embJ .mchk1))
            (pxEntry := embJ (.matrixP (.matP (.chk 0))))
            (exitPh := embJ .mchk1)
            (existFlag := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).existFlag)
            (allFlag := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).allFlag))
          (embJ (.gatesP (.chk 0))) (embJ (.matrixP (.igP (.chk 0))))
          (ep (.chk j.succ))
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).newSlot
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).gateFlag
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).initSt
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).storeCarry i ρ :=
    fun i ρ => hrulesM j i ρ
  have hback := dt.step_var_back F hrulesV hR hlin hvi
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (mval := st.val) (f := f₀)
    (by rw [ixBack_wk, hwkSt])
  have hupd : dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
      (dt.ixPostVarSt v st st.val (dt.varList.get j) False) v =
      Function.update (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)
        (dt.varArgsOf PR.zero PR.one (dt.varAt j)).newSlot PR.zero := by
    have h := dt.ixBack_postVarSt_v (zero := PR.zero) (one := PR.one) F v
      (st := st) (m := st.val) (i := dt.varList.get j) (b := False)
    rw [bitVal_neg not_false] at h
    exact h
  have hmach := ixVarMachineFail_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
    (hix := hix) (hinj := hinj) (heltP := heltP)
    (vi := dt.varAt j) (st := st) (hrules := hrulesJ) (hR := hR) (hlin := hlin)
    (htop := htop) (hbot := hbot) (hv := hv) (hvi := hvi) (hwkSt := hwkSt)
    (hgap := hgap) (w := w) (wP := wP) (hwP := hwP) (hcostR := hcostR)
    (TestOf := TestOf) (hcompatOf := hcompatOf) (tOf := tOf)
    (htagOf := htagOf) (ℓ₀ := ℓ₀) (hTestLt := hTestLt) (hfail := hfail)
    (f₀ := f₀)
    (rest' := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
      (dt.ixPostVarSt v st st.val (dt.varList.get j) False))
    (hoff := fun r hr => (dt.ixBack_postVarSt_off (zero := PR.zero) (one := PR.one)
      (st := st) (m := st.val) (i := dt.varList.get j) (b := False) F v r hr).trans
      (congrArg (fun t => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le t r)
        (ixRoundSt_val st))) (hupd := hupd)
  refine TMData.ReachesIn.mono ?_ ((TMData.reachesIn_of_step hback).trans hmach)
  simp only [ixLegCost]
  have hj : dt.ixVarCost A (dt.varAt j) w wP wR wK (Nat.card ιV) ≤
      Finset.univ.sup fun j' : Fin dt.nv =>
        dt.ixVarCost A (dt.varAt j') w wP wR wK (Nat.card ιV) :=
    Finset.le_sup (f := fun j' : Fin dt.nv =>
      dt.ixVarCost A (dt.varAt j') w wP wR wK (Nat.card ιV)) (Finset.mem_univ j)
  have hG : 1 + dt.ixVarGatesCost A (dt.varAt j) w wP + 1 ≤
      dt.ixVarCost A (dt.varAt j) w wP wR wK (Nat.card ιV) := by
    simp only [ixVarCost]
    omega
  omega

include hrulesM hR hlin hix hsepP hhasP hinj heltP htop hbot hv hvi hgap hwP
  hcostR in
omit [LinearOrder ιV] [Finite ιV] in
/-- **One spine position's leg at a shaped but ungated address**: the
walk-back, the whole gate sequence — every file test passing, the total
dispatch carrying every block through — the clear flag at the verdict
checkpoint, and the erased stage slot at the marker: the verdict `False`,
the VAL register untouched. With
`DescriptiveComplexity.Draw.Data.ixVarLeg_run` and
`DescriptiveComplexity.Draw.Data.ixVarLegFail_run` this covers **every**
address the sweep visits. -/
theorem ixVarLegUngated_reachesIn (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (hwkSt : st.wk = fun r => r = v)
    (TestOf : Fin (dt.arOf (dt.varAt j)) → I → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (dt.varAt j))) (u : I),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
        (PR.passTracksAt F.cell Slot.mir (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
          st.mir (F.cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (dt.varAt j)) → dt.X.Tag)
    (htagOf : ∀ ℓ : Fin (dt.arOf (dt.varAt j)),
      dt.dspTagOf PR.zero PR.one
        (wmBlk (ixAddr elt st.mir)
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            Tag R P dt.KIx)) = tOf ℓ)
    (hTestOf : ∀ ℓ u, TestOf ℓ u)
    (ℓ₀ : Fin (dt.arOf (dt.varAt j)))
    (hbad : ¬((∀ t' : dt.X.Tag,
        wmBlk (ixAddr elt st.mir)
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ₀) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            Tag R P dt.KIx)
          (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ₀) ∧
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ₀, decRho dt.ly PR.zero PR.one
          (wmBlk (ixAddr elt st.mir)
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ₀) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R P dt.KIx)))))
    (f₀ : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx
      dt.dd)).ReachesIn (dt.ixLegCost A w wP wR wK (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (ep (.sub (dt.smEntry j))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (ep (.chk j.succ))
          (dt.ixUngatedCtl (PR := PR) (v := v) F hhasP (dt.varAt j) st tOf
            ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt f₀
              (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)))), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixPostVarSt v st st.val (dt.varList.get j) False))
          st.val) (PR.syElt PR.blank)⟩ := by
  classical
  set embJ : dt.VarPhF (dt.varAt j) → P :=
    fun p => ep (.sub (Sum.inl ⟨j, p⟩)) with hembJ
  have hrulesJ : ∀ (i : dt.VarSiteF (dt.varAt j))
      (ρ : dt.VarShF (dt.varAt j) i),
      PR.rules (rEmbM j i ρ) =
        dt.varRuleF PR.zero PR.one (dt.varAt j)
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)) embJ
          (ep (.chk j.succ)) i ρ :=
    fun i ρ => hrulesM j i ρ
  have hrulesV : ∀ (i : dt.VarSiteF (dt.varAt j))
      (ρ : dt.VarShF (dt.varAt j) i),
      PR.rules (rEmbM j i ρ) =
        dt.varRule PR.zero PR.one embJ
          (dt.gatesRule (one := PR.one) (v := dt.varAt j)
            (emb := fun p => embJ (.gatesP p))
            (argsG := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsG)
            (wellGOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).wellGOf)
            (setFail := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).setFail)
            (enterSt :=
              (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterBlockSt)
            (failPh := embJ .vchk1) (exitPh := embJ .vchk1))
          (dt.roundRule (one := PR.one) (emb := fun p => embJ (.matrixP p))
            (ruleG := dt.igatesRule (one := PR.one) (v := dt.varAt j)
              (emb := fun p => embJ (.matrixP (.igP p)))
              (argsG := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsIG)
              (wellGOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).wellIGOf)
              (setFailOf := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).setFailIGOf)
              (enterSt := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterIGSt)
              (exitPh := embJ (.matrixP .rchk)))
            (ruleX := dt.matrixRule (zero := PR.zero) (one := PR.one)
              (v := dt.varAt j)
              (emb := fun p => embJ (.matrixP (.matP p)))
              (argsA := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).argsA)
              (enterSt := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterAtomSt)
              (exitPh := embJ .mchk1))
            (pxEntry := embJ (.matrixP (.matP (.chk 0))))
            (exitPh := embJ .mchk1)
            (existFlag := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).existFlag)
            (allFlag := (dt.varArgsOf PR.zero PR.one (dt.varAt j)).allFlag))
          (embJ (.gatesP (.chk 0))) (embJ (.matrixP (.igP (.chk 0))))
          (ep (.chk j.succ))
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).newSlot
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).gateFlag
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).initSt
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).postFold
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).storeCarry i ρ :=
    fun i ρ => hrulesM j i ρ
  have hback := dt.step_var_back F hrulesV hR hlin hvi
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (mval := st.val) (f := f₀)
    (by rw [ixBack_wk, hwkSt])
  have hupd : dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
      (dt.ixPostVarSt v st st.val (dt.varList.get j) False) v =
      Function.update (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v)
        (dt.varArgsOf PR.zero PR.one (dt.varAt j)).newSlot PR.zero := by
    have h := dt.ixBack_postVarSt_v (zero := PR.zero) (one := PR.one) F v
      (st := st) (m := st.val) (i := dt.varList.get j) (b := False)
    rw [bitVal_neg not_false] at h
    exact h
  have hmach := ixVarMachineUngated_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
    (hix := hix) (hinj := hinj) (heltP := heltP)
    (vi := dt.varAt j) (st := st) (hrules := hrulesJ) (hR := hR) (hlin := hlin)
    (htop := htop) (hbot := hbot) (hv := hv) (hvi := hvi) (hwkSt := hwkSt)
    (hgap := hgap) (w := w) (wP := wP) (hwP := hwP) (hcostR := hcostR)
    (TestOf := TestOf) (hcompatOf := hcompatOf) (tOf := tOf)
    (htagOf := htagOf) (hTestOf := hTestOf) (ℓ₀ := ℓ₀) (hbad := hbad)
    (f₀ := f₀)
    (rest' := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
      (dt.ixPostVarSt v st st.val (dt.varList.get j) False))
    (hoff := fun r hr => (dt.ixBack_postVarSt_off (zero := PR.zero) (one := PR.one)
      (st := st) (m := st.val) (i := dt.varList.get j) (b := False) F v r hr).trans
      (congrArg (fun t => dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le t r)
        (ixRoundSt_val st))) (hupd := hupd)
  refine TMData.ReachesIn.mono ?_ ((TMData.reachesIn_of_step hback).trans hmach)
  simp only [ixLegCost]
  have hj : dt.ixVarCost A (dt.varAt j) w wP wR wK (Nat.card ιV) ≤
      Finset.univ.sup fun j' : Fin dt.nv =>
        dt.ixVarCost A (dt.varAt j') w wP wR wK (Nat.card ιV) :=
    Finset.le_sup (f := fun j' : Fin dt.nv =>
      dt.ixVarCost A (dt.varAt j') w wP wR wK (Nat.card ιV)) (Finset.mem_univ j)
  have hG : 1 + dt.ixVarGatesCost A (dt.varAt j) w wP + 1 ≤
      dt.ixVarCost A (dt.varAt j) w wP wR wK (Nat.card ιV) := by
    simp only [ixVarCost]
    omega
  omega

/-! ### The output's leg

The out machinery is the same shape at `vi := none`, entered by the walk
home after a passed convergence sweep, its exit the accepting phase. Its
stage slot is the working-cell marker itself, so an accepting verdict's
write is idempotent — the tape after the leg is the machinery's own end
tape. -/

/-- **The VAL-loop thread of the output's leg**, at the entry-wrapped
control. -/
noncomputable def ixOutFM
    (st : TapeSt dt A R P I)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one none (dt.ixRoundSt st (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.IxKindSem PR.zero PR.one none (dt.ixRoundSt st (mV a))
          elt (dt.kindOf none b))
    (f₀ : dt.CtlIx → A) : ιV → dt.CtlIx → A :=
  dt.ixVarFM (elt := elt) F hinj hhasP heltP none st v mV semOf
    (dt.ixGatesFs F PR.zero PR.one hhasP none st v
      (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
      dt.card_le_ntgDim
      (fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag => (dt.domPk t').n)
        (Finset.mem_univ t)) dt.domDepth_le_eDim)
      (fun t => le_trans (Finset.le_sup
        (f := fun t' : dt.X.Tag =>
          (blkAtoms (dt.domPk t').mat).length)
        (Finset.mem_univ t)) dt.domReads_le_nfDim)
      tOf (dt.varArgsOf PR.zero PR.one none).enterBlockSt
      ((dt.varArgsOf PR.zero PR.one none).enterSt f₀
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))
      (dt.arOf (none : dt.VarIx)))

/-- **The control after the output's leg**: the out machinery's exit
fold. -/
noncomputable def ixOutCtl
    (st : TapeSt dt A R P I)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one none (dt.ixRoundSt st (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.IxKindSem PR.zero PR.one none (dt.ixRoundSt st (mV a))
          elt (dt.kindOf none b))
    (f₀ : dt.CtlIx → A) : dt.CtlIx → A :=
  (dt.varArgsOf PR.zero PR.one none).postFold
    (dt.ixRoundFX (elt := elt) F hinj hhasP heltP none st v mV semOf
      (dt.ixVarFM (elt := elt) F hinj hhasP heltP none st v mV semOf
        (dt.ixGatesFs F PR.zero PR.one hhasP none st v
          (fun ℓ => Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
          dt.card_le_ntgDim
          (fun t => le_trans (Finset.le_sup
            (f := fun t' : dt.X.Tag => (dt.domPk t').n)
            (Finset.mem_univ t)) dt.domDepth_le_eDim)
          (fun t => le_trans (Finset.le_sup
            (f := fun t' : dt.X.Tag =>
              (blkAtoms (dt.domPk t').mat).length)
            (Finset.mem_univ t)) dt.domReads_le_nfDim)
          tOf (dt.varArgsOf PR.zero PR.one none).enterBlockSt
          ((dt.varArgsOf PR.zero PR.one none).enterSt f₀
            (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))
          (dt.arOf (none : dt.VarIx))) aT) aT)
    (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)) v)

include hrulesOut hR hlin hix hsepP hhasP hinj heltP hord he₀ htop hbot hwork hv hvi
  hmono hup hvh hxdUse hgap hwP hwR hwK hcostR hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **The output's leg**: from the walk home's landing one cell right of
the marker, back to it, through the out machinery, and — the verdict
holding — out into the accepting phase, the marker rewritten with the
value it already carries. -/
theorem ixOutLeg_run
    (st : TapeSt dt A R P I)
    (hwkSt : st.wk = fun r => r = v)
    (TestOf : Fin (dt.arOf (none : dt.VarIx)) → I → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (u : I),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
        (PR.passTracksAt F.cell Slot.mir (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
          st.mir (F.cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (hwitOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (t' : dt.X.Tag),
      wmBlk (ixAddr elt st.mir)
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko none) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R P dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hmir : st.mir = ixMark elt v)
    (hbotSt : st.bot = fun r => r = (fun _ => False))
    (hsav : st.sav = ixMark elt v) (htgt : st.tgt = ixMark elt v)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one none (dt.ixRoundSt st (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.IxKindSem PR.zero PR.one none (dt.ixRoundSt st (mV a))
          elt (dt.kindOf none b))
    (hDom : ∀ ℓ : Fin (dt.arOf (none : dt.VarIx)),
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk (ixAddr elt st.mir)
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko none) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R P dt.KIx))))
    (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A)
    (hacc : (dt.varArgsOf PR.zero PR.one none).accBit
      (dt.ixOutCtl (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st tOf semOf f₀)) :
    (wideData (Univ A R P dt.KIx
      dt.dd)).ReachesIn (dt.ixOutLegCost A w wP wR wK (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (ep (.sub (dt.smEntryOut))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt accPh
          (dt.ixOutCtl (elt := elt)
            (v := v) (aT := aT) F hinj hhasP heltP mV st tOf semOf f₀)), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)))
          (mV aT)) (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  set embO : dt.VarPhF (none : dt.VarIx) → P :=
    fun p => ep (.sub (Sum.inr p)) with hembO
  have hrulesJ : ∀ (i : dt.VarSiteF (none : dt.VarIx))
      (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmbO i ρ) =
        dt.varRuleF PR.zero PR.one none
          (dt.varArgsOf PR.zero PR.one none) embO accPh i ρ :=
    fun i ρ => hrulesOut i ρ
  have hrulesV : ∀ (i : dt.VarSiteF (none : dt.VarIx))
      (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmbO i ρ) =
        dt.varRule PR.zero PR.one embO
          (dt.gatesRule (one := PR.one) (v := (none : dt.VarIx))
            (emb := fun p => embO (.gatesP p))
            (argsG := (dt.varArgsOf PR.zero PR.one none).argsG)
            (wellGOf := (dt.varArgsOf PR.zero PR.one none).wellGOf)
            (setFail := (dt.varArgsOf PR.zero PR.one none).setFail)
            (enterSt :=
              (dt.varArgsOf PR.zero PR.one none).enterBlockSt)
            (failPh := embO .vchk1) (exitPh := embO .vchk1))
          (dt.roundRule (one := PR.one) (emb := fun p => embO (.matrixP p))
            (ruleG := dt.igatesRule (one := PR.one) (v := (none : dt.VarIx))
              (emb := fun p => embO (.matrixP (.igP p)))
              (argsG := (dt.varArgsOf PR.zero PR.one none).argsIG)
              (wellGOf := (dt.varArgsOf PR.zero PR.one none).wellIGOf)
              (setFailOf := (dt.varArgsOf PR.zero PR.one none).setFailIGOf)
              (enterSt := (dt.varArgsOf PR.zero PR.one none).enterIGSt)
              (exitPh := embO (.matrixP .rchk)))
            (ruleX := dt.matrixRule (zero := PR.zero) (one := PR.one)
              (v := (none : dt.VarIx))
              (emb := fun p => embO (.matrixP (.matP p)))
              (argsA := (dt.varArgsOf PR.zero PR.one none).argsA)
              (enterSt := (dt.varArgsOf PR.zero PR.one none).enterAtomSt)
              (exitPh := embO .mchk1))
            (pxEntry := embO (.matrixP (.matP (.chk 0))))
            (exitPh := embO .mchk1)
            (existFlag := (dt.varArgsOf PR.zero PR.one none).existFlag)
            (allFlag := (dt.varArgsOf PR.zero PR.one none).allFlag))
          (embO (.gatesP (.chk 0))) (embO (.matrixP (.igP (.chk 0)))) accPh
          (dt.varArgsOf PR.zero PR.one none).newSlot
          (dt.varArgsOf PR.zero PR.one none).gateFlag
          (dt.varArgsOf PR.zero PR.one none).accBit
          (dt.varArgsOf PR.zero PR.one none).enterSt
          (dt.varArgsOf PR.zero PR.one none).initSt
          (dt.varArgsOf PR.zero PR.one none).postFold
          (dt.varArgsOf PR.zero PR.one none).storeCarry i ρ :=
    fun i ρ => hrulesOut i ρ
  -- the walk back to the marker
  have hback := dt.step_var_back F hrulesV hR hlin hvi
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (mval := st.val) (f := f₀)
    (by rw [ixBack_wk, hwkSt])
  -- the machinery
  have hmach := ixVarMachine_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
    (hix := hix) (hinj := hinj) (heltP := heltP) (he₀ := he₀)
    (hord := hord) (vi := none) (st := st) (hrules := hrulesJ) (hR := hR)
    (hlin := hlin) (htop := htop) (hbot := hbot) (hwork := hwork) (hv := hv)
    (hvi := hvi) (hwkSt := hwkSt) (hmono := hmono) (hup := hup) (hvh := hvh)
    (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR) (hwK := hwK)
    (hcostR := hcostR) (TestOf := TestOf) (hcompatOf := hcompatOf)
    (tOf := tOf) (hbotV := hbotV) (htopV := htopV) (mV := mV) (hmV0 := hmV0)
    (hIncr := hIncr) (hTestT := hTestT) (hTestF := hTestF) (hmir := hmir)
    (hbotSt := hbotSt) (hsav := hsav) (htgt := htgt) (semOf := semOf)
    (hDom := hDom) (hwitOf := hwitOf) (hTestOf := hTestOf) (f₀ := f₀)
  -- the accepting exit: the marker rewritten with its own value
  have hupd : dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)) v =
      Function.update
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)) v)
        ((dt.varArgsOf PR.zero PR.one none).newSlot)
        (bitVal PR.zero PR.one
          ((dt.varArgsOf PR.zero PR.one none).accBit
            (dt.ixOutCtl (elt := elt)
              (v := v) (aT := aT) F hinj hhasP heltP mV st tOf semOf f₀))) := by
    funext sl
    by_cases hs : sl = (dt.varArgsOf PR.zero PR.one none).newSlot
    · subst hs
      rw [Function.update_self]
      change dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)) v
        Slot.wk = _
      rw [ixBack_wk]
      change bitVal PR.zero PR.one (st.wk v) = _
      rw [hwkSt, bitVal_pos rfl, bitVal_pos hacc]
    · rw [Function.update_of_ne hs]
  have hns : (dt.varArgsOf PR.zero PR.one (none : dt.VarIx)).newSlot ≠
      Slot.val := fun h => nomatch h
  have hexit := dt.step_var_exit F hrulesV hR hlin hix hbot hv hvi
    (f := dt.ixOutCtl (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st tOf semOf f₀)
    (dt.ixVarBg_back F hix htop (dt.ixRoundSt st (mV aT)) hwkSt) hns
    (fun _ _ => rfl) hupd
  refine TMData.ReachesIn.mono (le_of_eq ?_)
    (((TMData.reachesIn_of_step hback).trans hmach).tail hexit)
  rw [ixOutLegCost]

include hrulesOut hR hlin hix hsepP hhasP hinj heltP hord he₀ htop hbot hwork hv hvi
  hmono hup hvh hxdUse hgap hwP hwR hwK hcostR hbotV htopV hmV0 hIncr hTestT
  hTestF in
open Classical in
/-- **The output's leg, whatever the verdict**: `ixOutLeg_run` with the
verdict not assumed. The run is the same run – the exit fires either way – and
what changes is only what it writes at the marker: the verdict's own bit. This
is what a *backward* reading needs, where the verdict is what is being
determined rather than assumed. -/
theorem ixOutLeg_run_any
    (st : TapeSt dt A R P I)
    (hwkSt : st.wk = fun r => r = v)
    (TestOf : Fin (dt.arOf (none : dt.VarIx)) → I → Prop)
    (hcompatOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (u : I),
      dt.wellShapedG PR.zero PR.one
        (Sum.inl (Fin.castLE (dt.arOf_le_ko none) ℓ))
        (PR.passTracksAt F.cell Slot.mir (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st)
          st.mir (F.cell u)) ↔ TestOf ℓ u)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (hwitOf : ∀ (ℓ : Fin (dt.arOf (none : dt.VarIx))) (t' : dt.X.Tag),
      wmBlk (ixAddr elt st.mir)
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko none) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R P dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = tOf ℓ)
    (hmir : st.mir = ixMark elt v)
    (hbotSt : st.bot = fun r => r = (fun _ => False))
    (hsav : st.sav = ixMark elt v) (htgt : st.tgt = ixMark elt v)
    (semOf : ∀ a : ιV,
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one none (dt.ixRoundSt st (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.IxKindSem PR.zero PR.one none (dt.ixRoundSt st (mV a))
          elt (dt.kindOf none b))
    (hDom : ∀ ℓ : Fin (dt.arOf (none : dt.VarIx)),
      ExpExpansion.DomHolds (X := dt.X)
        (tOf ℓ, decRho dt.ly PR.zero PR.one
          (wmBlk (ixAddr elt st.mir)
            (Tag.arg (toLex ((Sum.inl
              (Fin.castLE (dt.arOf_le_ko none) ℓ) :
              Fin dt.ko ⊕ Fin dt.ki))) :
              Tag R P dt.KIx))))
    (hTestOf : ∀ ℓ u, TestOf ℓ u) (f₀ : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx
      dt.dd)).ReachesIn (dt.ixOutLegCost A w wP wR wK (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (ep (.sub (dt.smEntryOut))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt accPh
          (dt.ixOutCtl (elt := elt)
            (v := v) (aT := aT) F hinj hhasP heltP mV st tOf semOf f₀)), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (fun r => if r = v then
              Function.update
                (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
                  (dt.ixRoundSt st (mV aT)) v)
                (dt.varArgsOf PR.zero PR.one none).newSlot
                (bitVal PR.zero PR.one
                  ((dt.varArgsOf PR.zero PR.one none).accBit
                    (dt.ixOutCtl (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
                      mV st tOf semOf f₀)))
            else dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
              (dt.ixRoundSt st (mV aT)) r)
          (mV aT)) (PR.syElt PR.blank)⟩ := by
  classical
  have hzo := PR.zero_ne_one
  set embO : dt.VarPhF (none : dt.VarIx) → P :=
    fun p => ep (.sub (Sum.inr p)) with hembO
  have hrulesJ : ∀ (i : dt.VarSiteF (none : dt.VarIx))
      (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmbO i ρ) =
        dt.varRuleF PR.zero PR.one none
          (dt.varArgsOf PR.zero PR.one none) embO accPh i ρ :=
    fun i ρ => hrulesOut i ρ
  have hrulesV : ∀ (i : dt.VarSiteF (none : dt.VarIx))
      (ρ : dt.VarShF (none : dt.VarIx) i),
      PR.rules (rEmbO i ρ) =
        dt.varRule PR.zero PR.one embO
          (dt.gatesRule (one := PR.one) (v := (none : dt.VarIx))
            (emb := fun p => embO (.gatesP p))
            (argsG := (dt.varArgsOf PR.zero PR.one none).argsG)
            (wellGOf := (dt.varArgsOf PR.zero PR.one none).wellGOf)
            (setFail := (dt.varArgsOf PR.zero PR.one none).setFail)
            (enterSt :=
              (dt.varArgsOf PR.zero PR.one none).enterBlockSt)
            (failPh := embO .vchk1) (exitPh := embO .vchk1))
          (dt.roundRule (one := PR.one) (emb := fun p => embO (.matrixP p))
            (ruleG := dt.igatesRule (one := PR.one) (v := (none : dt.VarIx))
              (emb := fun p => embO (.matrixP (.igP p)))
              (argsG := (dt.varArgsOf PR.zero PR.one none).argsIG)
              (wellGOf := (dt.varArgsOf PR.zero PR.one none).wellIGOf)
              (setFailOf := (dt.varArgsOf PR.zero PR.one none).setFailIGOf)
              (enterSt := (dt.varArgsOf PR.zero PR.one none).enterIGSt)
              (exitPh := embO (.matrixP .rchk)))
            (ruleX := dt.matrixRule (zero := PR.zero) (one := PR.one)
              (v := (none : dt.VarIx))
              (emb := fun p => embO (.matrixP (.matP p)))
              (argsA := (dt.varArgsOf PR.zero PR.one none).argsA)
              (enterSt := (dt.varArgsOf PR.zero PR.one none).enterAtomSt)
              (exitPh := embO .mchk1))
            (pxEntry := embO (.matrixP (.matP (.chk 0))))
            (exitPh := embO .mchk1)
            (existFlag := (dt.varArgsOf PR.zero PR.one none).existFlag)
            (allFlag := (dt.varArgsOf PR.zero PR.one none).allFlag))
          (embO (.gatesP (.chk 0))) (embO (.matrixP (.igP (.chk 0)))) accPh
          (dt.varArgsOf PR.zero PR.one none).newSlot
          (dt.varArgsOf PR.zero PR.one none).gateFlag
          (dt.varArgsOf PR.zero PR.one none).accBit
          (dt.varArgsOf PR.zero PR.one none).enterSt
          (dt.varArgsOf PR.zero PR.one none).initSt
          (dt.varArgsOf PR.zero PR.one none).postFold
          (dt.varArgsOf PR.zero PR.one none).storeCarry i ρ :=
    fun i ρ => hrulesOut i ρ
  -- the walk back to the marker
  have hback := dt.step_var_back F hrulesV hR hlin hvi
    (rest := dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) (mval := st.val) (f := f₀)
    (by rw [ixBack_wk, hwkSt])
  -- the machinery
  have hmach := ixVarMachine_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
    (hix := hix) (hinj := hinj) (heltP := heltP) (he₀ := he₀)
    (hord := hord) (vi := none) (st := st) (hrules := hrulesJ) (hR := hR)
    (hlin := hlin) (htop := htop) (hbot := hbot) (hwork := hwork) (hv := hv)
    (hvi := hvi) (hwkSt := hwkSt) (hmono := hmono) (hup := hup) (hvh := hvh)
    (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR) (hwK := hwK)
    (hcostR := hcostR) (TestOf := TestOf) (hcompatOf := hcompatOf)
    (tOf := tOf) (hbotV := hbotV) (htopV := htopV) (mV := mV) (hmV0 := hmV0)
    (hIncr := hIncr) (hTestT := hTestT) (hTestF := hTestF) (hmir := hmir)
    (hbotSt := hbotSt) (hsav := hsav) (htgt := htgt) (semOf := semOf)
    (hDom := hDom) (hwitOf := hwitOf) (hTestOf := hTestOf) (f₀ := f₀)
  -- the accepting exit: the marker rewritten with the verdict, whichever it is
  classical
  have hns : (dt.varArgsOf PR.zero PR.one (none : dt.VarIx)).newSlot ≠
      Slot.val := fun h => nomatch h
  have hexit := dt.step_var_exit F hrulesV hR hlin hix hbot hv hvi
    (f := dt.ixOutCtl (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st tOf semOf f₀)
    (rest' := fun r => if r = v then
        Function.update
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)) v)
          (dt.varArgsOf PR.zero PR.one none).newSlot
          (bitVal PR.zero PR.one
            ((dt.varArgsOf PR.zero PR.one none).accBit
              (dt.ixOutCtl (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP
                mV st tOf semOf f₀)))
      else dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le (dt.ixRoundSt st (mV aT)) r)
    (dt.ixVarBg_back F hix htop (dt.ixRoundSt st (mV aT)) hwkSt) hns
    (fun r hr => if_neg hr) (if_pos rfl)
  refine TMData.ReachesIn.mono (le_of_eq ?_)
    (((TMData.reachesIn_of_step hback).trans hmach).tail hexit)
  rw [ixOutLegCost]

/-- **The state the output's leg ends at — threaded**: the machinery's own
exit state, the accepting write at the marker being idempotent. -/
noncomputable def ixOutStE
    (st : TapeSt dt A R P I)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (semT : ∀ (p : IxScratch dt A R P I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one none (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.IxKindSem PR.zero PR.one none
          (dt.ixMatSt (elt := elt) none (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
          elt (dt.kindOf none b))
    (f₀ : dt.CtlIx → A) : TapeSt dt A R P I :=
  dt.ixVarStE (elt := elt) F hinj hhasP heltP
    none st v mV semT (dt.ixVarFG (PR := PR) F hhasP none st v tOf f₀) aT

/-- **The control after the output's leg — threaded**: the out machinery's
exit fold, at the states its own thread produces. -/
noncomputable def ixOutCtlT
    (st : TapeSt dt A R P I)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (semT : ∀ (p : IxScratch dt A R P I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one none (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.IxKindSem PR.zero PR.one none
          (dt.ixMatSt (elt := elt) none (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
          elt (dt.kindOf none b))
    (f₀ : dt.CtlIx → A) : dt.CtlIx → A :=
  (dt.varArgsOf PR.zero PR.one none).postFold
    (dt.ixVarFXT (elt := elt) F hinj hhasP heltP
      none st v mV semT (dt.ixVarFG (PR := PR) F hhasP none st v tOf f₀) aT)
    (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
      (dt.ixOutStE (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st tOf semT f₀) v)

open Classical in
/-- **The state the output's leg leaves, whatever its verdict**: the
machinery's exit state with the marker rewritten by the accepting bit — so
the marker survives a *true* verdict and is cleared by a false one, which is
what makes a false output halt and reject. -/
noncomputable def ixOutStA
    (st : TapeSt dt A R P I)
    (tOf : Fin (dt.arOf (none : dt.VarIx)) → dt.X.Tag)
    (semT : ∀ (p : IxScratch dt A R P I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (none : dt.VarIx)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one none (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (none : dt.VarIx)),
        dt.IxKindSem PR.zero PR.one none
          (dt.ixMatSt (elt := elt) none (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
          elt (dt.kindOf none b))
    (f₀ : dt.CtlIx → A) : TapeSt dt A R P I :=
  { dt.ixOutStE (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st tOf semT f₀ with
    wk := (fun r => r = v ∧ (dt.varArgsOf PR.zero PR.one none).accBit
      (dt.ixOutCtlT (elt := elt) (v := v) (aT := aT) F hinj hhasP heltP mV st tOf semT f₀)) }

/-! ### Which leg a position takes

A position's machinery has three runs, by what its gates do:
`DescriptiveComplexity.Draw.Data.ixVarLeg_run_thread` when every block is
well shaped *and* the tags and the domain sentence agree,
`DescriptiveComplexity.Draw.Data.ixVarLegUngated_run` when the blocks are
well shaped but the verdict flag is cleared, and
`DescriptiveComplexity.Draw.Data.ixVarLegFail_run` when a block fails the
shape test — which is the one that needs a witness, and a *least* one, so
that the blocks before it have run. -/

/-- **The shape test the gates run**, at a position and a state: the
per-cell question a block's `TestKit` asks, which is what tells the third
leg from the other two. -/
def ixShapeAt (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (ℓ : Fin (dt.arOf (dt.varAt j))) (u : I) : Prop :=
  dt.wellShapedG PR.zero PR.one
    (Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ))
    (PR.passTracksAt F.cell Slot.mir (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.mir
      (F.cell u))

/-- **The tag a block's witness cells name**, as the machine reads it —
so `htagOf` is `rfl` at this choice. -/
noncomputable def ixTagAt (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (ℓ : Fin (dt.arOf (dt.varAt j))) : dt.X.Tag :=
  dt.dspTagOf PR.zero PR.one
    (wmBlk (ixAddr elt st.mir)
      (Tag.arg (toLex ((Sum.inl (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
        Fin dt.ko ⊕ Fin dt.ki))) :
        Tag R P dt.KIx))

/-- **The other half of a block's gate**: its tag witnesses are one-hot at
the tag they name, and the expansion's domain sentence holds of the point
the block decodes. Together with
`DescriptiveComplexity.Draw.Data.ixShapeAt` this is the gates' verdict. -/
def ixTagDomAt (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (ℓ : Fin (dt.arOf (dt.varAt j))) : Prop :=
  (∀ t' : dt.X.Tag,
      wmBlk (ixAddr elt st.mir)
        (Tag.arg (toLex ((Sum.inl
          (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
          Fin dt.ko ⊕ Fin dt.ki))) :
          Tag R P dt.KIx)
        (encTagTup dt.ly PR.zero PR.one t') ↔ t' = dt.ixTagAt (PR := PR) (elt := elt) j st ℓ) ∧
    ExpExpansion.DomHolds (X := dt.X)
      (dt.ixTagAt (PR := PR) (elt := elt) j st ℓ, decRho dt.ly PR.zero PR.one
        (wmBlk (ixAddr elt st.mir)
          (Tag.arg (toLex ((Sum.inl
            (Fin.castLE (dt.arOf_le_ko (dt.varAt j)) ℓ) :
            Fin dt.ko ⊕ Fin dt.ki))) :
            Tag R P dt.KIx)))

/-- **A position is gated** when every block passes both halves. -/
def ixGatedAt (j : Fin dt.nv)
    (st : TapeSt dt A R P I) : Prop :=
  (∀ (ℓ : Fin (dt.arOf (dt.varAt j))) u, dt.ixShapeAt (PR := PR) (F := F) j st ℓ u) ∧
    ∀ ℓ : Fin (dt.arOf (dt.varAt j)), dt.ixTagDomAt (PR := PR) (elt := elt) j st ℓ

open Classical in
/-- **The state one position's leg leaves, whichever leg it takes**: the
machinery's own exit at a gated position, and the entry state with the
stage bit erased at the two ungated ones — which agree on the tape and
differ only in their control. -/
noncomputable def ixLegStB (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (semT : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st →
      ∀ (p : IxScratch dt A R P I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) : TapeSt dt A R P I :=
  if hg : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st then
    dt.ixLegStT (elt := elt) (aT := aT) F hinj hhasP heltP
      mV j st (dt.ixTagAt (PR := PR) (elt := elt) j st) (semT hg) f₀
  else dt.ixPostVarSt v st st.val (dt.varList.get j) False

open Classical in
/-- **The control one position's leg leaves**: the machinery's fold at a
gated position, the ungated exit when the blocks are well shaped but a tag
or the domain fails, and the failing gates' exit — at the *least* badly
shaped block — otherwise. -/
noncomputable def ixLegCtlB (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (semT : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st →
      ∀ (p : IxScratch dt A R P I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) : dt.CtlIx → A :=
  if hg : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st then
    dt.ixLegCtlT (elt := elt) (aT := aT) F hinj hhasP heltP
      mV j st (dt.ixTagAt (PR := PR) (elt := elt) j st) (semT hg) f₀
  else if hs : ∀ (ℓ : Fin (dt.arOf (dt.varAt j))) u,
      dt.ixShapeAt (PR := PR) (F := F) j st ℓ u then
    dt.ixUngatedCtl (PR := PR) (v := v) F hhasP (dt.varAt j) st (dt.ixTagAt (PR := PR) (elt := elt)
      j st)
      ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt f₀
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))
  else
    dt.ixFailCtl (PR := PR) (v := v) F hhasP (dt.varAt j) st (dt.ixTagAt (PR := PR) (elt := elt)
      j st)
      (exists_least_fail (T := dt.ixShapeAt (PR := PR) (F := F) j st) hs).choose
      ((dt.varArgsOf PR.zero PR.one (dt.varAt j)).enterSt f₀
        (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st v))

omit [Finite R] [Finite P] [Finite dt.KIx]
  [Finite ιV] [Finite I] in
/-- **What a leg leaves alone, whichever leg it takes**: the ungated legs
never enter the VAL loop, so they touch nothing but the stage bit, and the
gated one is `DescriptiveComplexity.Draw.Data.ixLegStT_fields`. The `val`
register is left out on purpose — it is the loop's top at a gated
position and the entry state's at the other two. -/
theorem ixLegStB_fields (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (semT : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st →
      ∀ (p : IxScratch dt A R P I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) :
    (dt.ixLegStB (elt := elt) (aT := aT) F hinj hhasP heltP mV j st semT f₀).mir = st.mir ∧
      (dt.ixLegStB (elt := elt) (aT := aT) F hinj hhasP heltP mV j st semT f₀).wk = st.wk ∧
      (dt.ixLegStB (elt := elt) (aT := aT) F hinj hhasP heltP mV j st semT f₀).bot = st.bot ∧
      (dt.ixLegStB (elt := elt) (aT := aT) F hinj hhasP heltP mV j st semT f₀).old = st.old ∧
      (dt.ixLegStB (elt := elt) (aT := aT) F hinj hhasP heltP mV j st semT f₀).ltp = st.ltp := by
  classical
  by_cases hg : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st
  · rw [show dt.ixLegStB (elt := elt) (aT := aT) F hinj hhasP heltP
    mV j st semT f₀ = _ from dif_pos hg]
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := dt.ixLegStT_fields (elt := elt) (aT := aT) F hinj hhasP heltP
      mV j st
      (dt.ixTagAt (PR := PR) (elt := elt) j st) (semT hg) f₀
    exact ⟨h1, h2, h3, h4, h5⟩
  · rw [show dt.ixLegStB (elt := elt) (aT := aT) F hinj hhasP heltP
    mV j st semT f₀ = _ from dif_neg hg]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

open Classical in
/-- **The stage bit one position writes**, whichever leg it takes: the
machinery's verdict at a gated position, `False` at the two ungated ones,
which is what the stage dictionary holds where the blocks encode no
point. -/
noncomputable def ixLegBitB (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (semT : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st →
      ∀ (p : IxScratch dt A R P I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) : Prop :=
  if hg : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st then
    (dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
      (dt.ixLegCtlT (elt := elt) (aT := aT) F hinj hhasP heltP
        mV j st (dt.ixTagAt (PR := PR) (elt := elt) j st) (semT hg) f₀)
  else False

omit [Finite R] [Finite P] [Finite dt.KIx]
  [Finite ιV] in
omit [Finite I] in
open Classical in
/-- **What a leg writes**: its variable's cell at the marker, and nothing
else — the same equation whichever leg it takes, since the VAL loop
threads the two scratch registers alone
(`DescriptiveComplexity.Draw.Data.ixVarStE_new`) and the ungated legs
write the stage bit directly. This is the branched twin of
`DescriptiveComplexity.Draw.Data.new_postVarSt`, and the only thing the
spine's dictionary lemmas need of a leg. -/
theorem ixLegStB_new (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (semT : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st →
      ∀ (p : IxScratch dt A R P I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) (i' : dt.d.B.ι)
    (r : Univ A R P dt.KIx dt.dd → Prop) :
    (dt.ixLegStB (elt := elt) (aT := aT) F hinj hhasP heltP mV j st semT f₀).new i' r =
      (if i' = dt.varList.get j ∧ r = v then
        dt.ixLegBitB (elt := elt) (aT := aT) F hinj hhasP heltP
          mV j st semT f₀ else st.new i' r) := by
  classical
  by_cases hg : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st
  · rw [show dt.ixLegStB (elt := elt) (aT := aT) F hinj hhasP heltP
    mV j st semT f₀ = _ from dif_pos hg,
      show dt.ixLegBitB (elt := elt) (aT := aT) F hinj hhasP heltP
        mV j st semT f₀ = _ from dif_pos hg, ixLegStT]
    exact congrArg
      (fun N : dt.d.B.ι →
          (Univ A R P dt.KIx dt.dd → Prop) →
          Prop =>
        if i' = dt.varList.get j ∧ r = v then
          (dt.varArgsOf PR.zero PR.one (dt.varAt j)).accBit
            (dt.ixLegCtlT (elt := elt) (aT := aT) F hinj hhasP heltP
              mV j st (dt.ixTagAt (PR := PR) (elt := elt) j st)
              (semT hg) f₀)
        else N i' r)
      (dt.ixVarStE_new (elt := elt) F hinj hhasP heltP (dt.varAt j) st mV (semT hg)
        (dt.ixVarFG (PR := PR) F hhasP (dt.varAt j) st v (dt.ixTagAt (PR := PR) (elt := elt)
          j st) f₀)
        aT)
  · rw [show dt.ixLegStB (elt := elt) (aT := aT) F hinj hhasP heltP
    mV j st semT f₀ = _ from dif_neg hg,
      show dt.ixLegBitB (elt := elt) (aT := aT) F hinj hhasP heltP
        mV j st semT f₀ = _ from dif_neg hg]
    rfl

include hrulesM hR hlin hix hsepP hhasP hinj heltP hord he₀ htop hbot hwork hv hvi
  hmono hup hvh hxdUse hgap hwP hwR hwK hcostR hbotV htopV hmV0 hIncr hTestT
  hTestF in
/-- **One spine position's leg, whichever leg it takes**: the three runs
of the machinery under one statement, the case split on the gates made
once and for all. This is what a sweep needs, since it visits junk
addresses and gated ones alike. -/
theorem ixVarLegB_reachesIn (j : Fin dt.nv)
    (st : TapeSt dt A R P I)
    (hwkSt : st.wk = fun r => r = v) (hmir : st.mir = ixMark elt v)
    (hbotSt : st.bot = fun r => r = (fun _ => False))
    (semT : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st →
      ∀ (p : IxScratch dt A R P I) (a : ιV),
      (∀ ℓ : Fin (dt.nIn (dt.varAt j)),
        dt.ixIGPassP (elt := elt) F PR.zero PR.one (dt.varAt j) (dt.ixVarRdSt st p (mV a)) ℓ) →
      ∀ b : Fin (dt.natOf (dt.varAt j)),
        dt.IxKindSem PR.zero PR.one (dt.varAt j)
          (dt.ixMatSt (elt := elt) (dt.varAt j) (dt.ixVarRdSt st p (mV a)) v (b : ℕ))
          elt (dt.kindOf (dt.varAt j) b))
    (f₀ : dt.CtlIx → A) :
    (wideData (Univ A R P dt.KIx
      dt.dd)).ReachesIn (dt.ixLegCost A w wP wR wK (Nat.card ιV))
      ⟨Sum.inr (PR.stElt (ep (.sub (dt.smEntry j))) f₀), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le st) st.val) (PR.syElt PR.blank)⟩
      ⟨Sum.inr (PR.stElt (ep (.chk j.succ))
          (dt.ixLegCtlB (elt := elt) (aT := aT) F hinj hhasP heltP mV j st semT f₀)), Sum.inl v',
        wideTape (PR.trackTapeAt F.cell Slot.val
          (dt.ixBack F.toLayout PR.zero PR.one dt.dd0Le
            (dt.ixLegStB (elt := elt) (aT := aT) F hinj hhasP heltP mV j st semT f₀))
          (dt.ixLegStB (elt := elt) (aT := aT) F hinj hhasP heltP mV j st semT f₀).val)
          (PR.syElt PR.blank)⟩ := by
  classical
  by_cases hg : dt.ixGatedAt (PR := PR) (elt := elt) (F := F) j st
  · -- gated: the whole machinery, threaded
    have hval : (dt.ixLegStT (elt := elt) (aT := aT) F hinj hhasP heltP
      mV j st (dt.ixTagAt (PR := PR) (elt := elt) j st)
        (semT hg) f₀).val = mV aT :=
      (dt.ixLegStT_fields (elt := elt) (aT := aT) F hinj hhasP heltP
        mV j st (dt.ixTagAt (PR := PR) (elt := elt) j st)
        (semT hg) f₀).2.2.2.2.2
    rw [show dt.ixLegStB (elt := elt) (aT := aT) F hinj hhasP heltP
      mV j st semT f₀ = _ from dif_pos hg,
      show dt.ixLegCtlB (elt := elt) (aT := aT) F hinj hhasP heltP
        mV j st semT f₀ = _ from dif_pos hg, hval]
    exact ixVarLeg_run_thread_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
      (hix := hix) (hinj := hinj) (heltP := heltP) (he₀ := he₀) (hord := hord)
      (hrulesM := hrulesM) (hR := hR) (hlin := hlin) (htop := htop)
      (hbot := hbot)
      (hwork := hwork) (hv := hv) (hvi := hvi) (hmono := hmono) (hup := hup)
      (hvh := hvh) (hxdUse := hxdUse) (hgap := hgap) (hwP := hwP) (hwR := hwR)
      (hwK := hwK) (hcostR := hcostR) (hbotV := hbotV) (htopV := htopV)
      (mV := mV) (hmV0 := hmV0) (hIncr := hIncr) (hTestT := hTestT)
      (hTestF := hTestF) (j := j) (st := st)
      (hwkSt := hwkSt) (TestOf := dt.ixShapeAt (PR := PR) (F := F) j st)
      (hcompatOf := fun _ _ => Iff.rfl)
      (tOf := dt.ixTagAt (PR := PR) (elt := elt) j st)
      (hwitOf := fun ℓ => (hg.2 ℓ).1) (hmir := hmir) (hbotSt := hbotSt)
      (semT := semT hg) (hDom := fun ℓ => (hg.2 ℓ).2) (hTestOf := hg.1) (f₀ := f₀)
  · rw [show dt.ixLegStB (elt := elt) (aT := aT) F hinj hhasP heltP
    mV j st semT f₀ = _ from dif_neg hg]
    by_cases hs : ∀ (ℓ : Fin (dt.arOf (dt.varAt j))) u,
        dt.ixShapeAt (PR := PR) (F := F) j st ℓ u
    · -- well shaped, but a tag or the domain fails: the ungated exit
      have hbad : ∃ ℓ₀, ¬dt.ixTagDomAt (PR := PR) (elt := elt) j st ℓ₀ := by
        by_contra hc
        exact hg ⟨hs, fun ℓ => not_not.mp (fun h => hc ⟨ℓ, h⟩)⟩
      obtain ⟨ℓ₀, hℓ₀⟩ := hbad
      rw [show dt.ixLegCtlB (elt := elt) (aT := aT) F hinj hhasP heltP mV j st semT f₀ = _ from
        (dif_neg hg).trans (dif_pos hs)]
      exact ixVarLegUngated_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
        (hix := hix) (hinj := hinj) (heltP := heltP)
        (hrulesM := hrulesM) (hR := hR) (hlin := hlin) (htop := htop)
        (hbot := hbot) (hv := hv) (hvi := hvi) (hgap := hgap) (w := w) (wP := wP)
        (wR := wR) (wK := wK) (ιV := ιV)
        (hwP := hwP) (hcostR := hcostR) (j := j) (st := st)
        (hwkSt := hwkSt) (TestOf := dt.ixShapeAt (PR := PR) (F := F) j st)
        (hcompatOf := fun _ _ => Iff.rfl)
        (tOf := dt.ixTagAt (PR := PR) (elt := elt) j st)
        (htagOf := fun _ => rfl) (hTestOf := hs) (ℓ₀ := ℓ₀)
        (hbad := hℓ₀) (f₀ := f₀)
    · -- a block is badly shaped: the failing gates, at the least one
      obtain ⟨u₀, hfail, hlt⟩ :=
        (exists_least_fail (T := dt.ixShapeAt (PR := PR) (F := F) j st) hs).choose_spec
      rw [show dt.ixLegCtlB (elt := elt) (aT := aT) F hinj hhasP heltP mV j st semT f₀ = _ from
        (dif_neg hg).trans (dif_neg hs)]
      exact ixVarLegFail_reachesIn (F := F) (hhasP := hhasP) (hsepP := hsepP)
        (hix := hix) (hinj := hinj) (heltP := heltP)
        (hrulesM := hrulesM) (hR := hR) (hlin := hlin) (htop := htop)
        (hbot := hbot) (hv := hv) (hvi := hvi) (hgap := hgap) (w := w) (wP := wP)
        (wR := wR) (wK := wK) (ιV := ιV)
        (hwP := hwP) (hcostR := hcostR) (j := j) (st := st)
        (hwkSt := hwkSt) (TestOf := dt.ixShapeAt (PR := PR) (F := F) j st)
        (hcompatOf := fun _ _ => Iff.rfl)
        (tOf := dt.ixTagAt (PR := PR) (elt := elt) j st)
        (htagOf := fun _ => rfl) (ℓ₀ := _) (hTestLt := hlt)
        (hfail := hfail) (f₀ := f₀)

end Leg

end Data

end Draw

end DescriptiveComplexity
