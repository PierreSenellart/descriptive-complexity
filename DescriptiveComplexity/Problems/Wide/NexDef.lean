/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpDefAsm
import DescriptiveComplexity.Problems.Wide.PfpDefLoop
import DescriptiveComplexity.Problems.Wide.PfpCtl
import DescriptiveComplexity.Problems.Wide.PfpOrd
import DescriptiveComplexity.Problems.Wide.NexEval

/-!
# The clocked program's rules are definable

A reduction has to *write its machine down*: the emitted table must be read off
the interpreted structure, which is what
`DescriptiveComplexity.Pfp.PfpData.reads_progFrom` asks, and what it asks of the
rules is that each of them be first-order definable in the sense of
`DescriptiveComplexity.Pfp.URulesDefinable`.

The clocked program shares its whole tower with the space-bounded one, so the
tower's definability (`DescriptiveComplexity.Pfp.PfpData.uRulesDefinable_varRuleF`)
serves unchanged; what is new is the **spine**, whose checkpoints have two rules
instead of three, and the **outer layer**, whose sweeps are specifications
rather than kits. Both are here, and so are the program's own two
specifications: `uRulesDefinable_nexProg` is the whole clocked rule set, and
what a *reduction* still owes is its own `VarArgs`, the same obligation the
space-bounded one already meets.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-! ### What the file's advance computes

The one thing a clocked program writes that is not a copy of a slot is its
sweep's **pointer**, and what it holds after a step is the next register's own
tuple. Below the last tuple of a block that is the tuple's lexicographic
successor, which is what the definability of the advance is read off. -/

section Advance

variable {A K : Type} [LinearOrder A] [Finite A] [LinearOrder K] [Finite K]
variable {dd : ℕ}

/-- **Within a block the advance is the tuple's own successor**: the layout
order is block-major and the tuples are ordered lexicographically, so below the
last tuple the next register is the same block at the next tuple. -/
theorem blkNext_snd_of_ne_tupTop [Nonempty A] {u : Wide.BlkIx K A dd}
    (hu : u.2 ≠ tupTop A dd) :
    (blkNext A K dd u).2 = tupNext u.2 := by
  classical
  have hlin := Wide.isLinOrd_blkLe K A dd
  have hnm : ¬IsMaxTup u.2 := by
    intro hmax
    exact hu ((Wide.isLinOrd_tupLeLex (A := A) (d := dd)).2.2.1 _ _
      (tupLeLex_tupTop A dd u.2)
      ((tupLeLex_iff_toLex_le _ _).mpr (by
        simpa using (tup_isTop_iff (A := A) (D := dd)).mpr hmax (toLex (tupTop A dd)))))
  have hcov : toLex u.2 ⋖ toLex (tupNext u.2) :=
    tupSucc_iff_covBy.mp (tupSucc_tupNext hnm)
  have hlt : WMLt (Wide.blkLe K A dd) u (u.1, tupNext u.2) := by
    refine ⟨Or.inr ⟨rfl, (tupLeLex_iff_toLex_le _ _).mpr (le_of_lt hcov.1)⟩, ?_⟩
    rintro (⟨-, hc⟩ | ⟨-, hc⟩)
    · exact hc rfl
    · exact absurd ((tupLeLex_iff_toLex_le _ _).mp hc) (not_le_of_gt hcov.1)
  have hmin : ∀ v : Wide.BlkIx K A dd, WMLt (Wide.blkLe K A dd) u v →
      Wide.blkLe K A dd (u.1, tupNext u.2) v := by
    rintro ⟨b', t'⟩ ⟨hle, hnle⟩
    rcases hle with ⟨hb, hne⟩ | ⟨hb, ht⟩
    · exact Or.inl ⟨hb, hne⟩
    · refine Or.inr ⟨hb, (tupLeLex_iff_toLex_le _ _).mpr ?_⟩
      have hlt' : toLex u.2 < toLex t' := by
        refine lt_of_le_of_ne ((tupLeLex_iff_toLex_le _ _).mp ht) fun hc => hnle ?_
        exact Or.inr ⟨hb.symm, (tupLeLex_iff_toLex_le _ _).mpr (le_of_eq hc.symm)⟩
      by_contra hc
      exact hcov.2 hlt' (lt_of_not_ge hc)
  have hs := ixSucc_blkNext A K dd ⟨(u.1, tupNext u.2), hlt⟩
  exact congrArg Prod.snd
    (hlin.2.2.1 _ _ (hs.2 _ hlt) (hmin _ hs.1))

variable (K) in
/-- **The greatest block**: the last of the layout's blocks, which is a fact
about the block order alone and not about the instance. -/
noncomputable def blkTopB [Nonempty K] : Option K :=
  (exists_greatest (Le := Wide.blkTagLe K) (Wide.isLinOrd_blkTagLe K)
    (P := fun _ => True) ⟨none, trivial⟩).choose

/-- **The last register's block is that greatest block**: the layout order is
block-major, so the greatest index sits in the greatest block whatever the
instance. This is what makes the sweep's stop test a question the formula can be
built from – it compares the phase's block with a constant. -/
theorem fst_blkTop [Nonempty A] [Nonempty K] :
    (blkTop A K dd).1 = blkTopB K := by
  have hgeB : ∀ b : Option K, Wide.blkTagLe K b (blkTopB K) :=
    fun b => (exists_greatest (Le := Wide.blkTagLe K) (Wide.isLinOrd_blkTagLe K)
      (P := fun _ => True) ⟨none, trivial⟩).choose_spec.2 b trivial
  have hgeT : ∀ b : Option K, Wide.blkTagLe K b (blkTop A K dd).1 := by
    intro b
    rcases blkLe_blkTop A K dd (b, fun _ => Classical.arbitrary A) with ⟨hb, -⟩ | ⟨hb, -⟩
    · exact hb
    · exact hb ▸ (Wide.isLinOrd_blkTagLe K).1 b
  exact (Wide.isLinOrd_blkTagLe K).2.2.1 _ _ (hgeB _) (hgeT _)

/-- **The first register's tuple is the least element everywhere**: the layout
order is block-major and lexicographic within a block, so the least index of a
block carries the least tuple. This is what the sweep's exit writes into the
pointer when it resets to the file's first register. -/
theorem snd_blkBot_apply [Nonempty A] [Nonempty K] {zero : A}
    (hbot : ∀ a : A, zero ≤ a) (j : Fin dd) :
    (blkBot A K dd).2 j = zero := by
  rcases blkLe_blkBot A K dd ((blkBot A K dd).1, fun _ => zero) with ⟨-, hne⟩ | ⟨-, ht⟩
  · exact absurd rfl hne
  · rcases ht with hEq | ⟨j', -, hlt⟩
    · exact congrFun hEq j
    · exact absurd (hbot ((blkBot A K dd).2 j')) (not_le_of_gt hlt)

omit [Finite A] in
/-- **The least tuple is below every tuple**: at the first differing coordinate
the least element is smaller, which is what the lexicographic order asks. -/
theorem tupLeLex_const_bot [Nonempty A] {zero : A} (hbot : ∀ a : A, zero ≤ a)
    (t : Fin dd → A) : tupLeLex (fun _ : Fin dd => zero) t := by
  classical
  by_cases hEq : (fun _ : Fin dd => zero) = t
  · exact Or.inl hEq
  · have hne : ∃ j : Fin dd, zero ≠ t j := by
      by_contra hno
      exact hEq (funext fun j => not_not.mp fun h => hno ⟨j, h⟩)
    have hSne : (Finset.univ.filter fun j : Fin dd => zero ≠ t j).Nonempty :=
      ⟨hne.choose, by simp [hne.choose_spec]⟩
    refine Or.inr ⟨(Finset.univ.filter fun j : Fin dd => zero ≠ t j).min' hSne,
      fun i hi => ?_, ?_⟩
    · by_contra hc
      have hiS : i ∈ Finset.univ.filter fun j : Fin dd => zero ≠ t j := by
        simp [hc]
      exact absurd ((Finset.univ.filter fun j : Fin dd => zero ≠ t j).min'_le i hiS)
        (not_le_of_gt hi)
    · have hmem := (Finset.univ.filter fun j : Fin dd => zero ≠ t j).min'_mem hSne
      simp only [Finset.mem_filter] at hmem
      exact lt_of_le_of_ne (hbot _) hmem.2

omit [Finite K] in
/-- **Above the last tuple of a block lies another block**: nothing in the block
is above its last tuple, so a strictly greater index has a strictly greater
block. -/
theorem blkTag_lt_of_gt_tupTop [Nonempty A] {b : Option K} {v : Wide.BlkIx K A dd}
    (h : WMLt (Wide.blkLe K A dd) (b, tupTop A dd) v) :
    Wide.blkTagLe K b v.1 ∧ b ≠ v.1 := by
  rcases h.1 with ⟨hb, hne⟩ | ⟨hb, ht⟩
  · exact ⟨hb, hne⟩
  · exfalso
    have hEq : v.2 = tupTop A dd :=
      (Wide.isLinOrd_tupLeLex (A := A) (d := dd)).2.2.1 _ _
        (tupLeLex_tupTop A dd v.2) ht
    exact h.2 (Or.inr ⟨hb.symm, Or.inl (by rw [hEq])⟩)

variable (K) in
/-- **The next block, as a fact about the block order**: the least block above
this one, or this one if there is none. -/
noncomputable def blkNextTag [Nonempty K] (b : Option K) : Option K :=
  open Classical in
  if h : ∃ c : Option K, WMLt (Wide.blkTagLe K) b c then
    (exists_ixSucc (Wide.blkTagLe K) (Wide.isLinOrd_blkTagLe K) h).choose
  else b

/-- **The sweep's next block is that one**, so it is chosen when the formula is
built and not at the instance – which is what a destination phase being a
constant asks for. -/
theorem blkNextB_eq [Nonempty A] [Nonempty K] (b : Option K) :
    blkNextB A K dd b = blkNextTag K b := by
  classical
  have hlin := Wide.isLinOrd_blkLe K A dd
  have hlinB := Wide.isLinOrd_blkTagLe K
  by_cases hex : ∃ c : Option K, WMLt (Wide.blkTagLe K) b c
  · have hsucc := (exists_ixSucc (Wide.blkTagLe K) hlinB hex).choose_spec
    rw [blkNextTag, dif_pos hex]
    -- the index above `(b, tupTop)` exists, its block is above `b`
    have hlt : WMLt (Wide.blkLe K A dd) (b, tupTop A dd)
        ((exists_ixSucc (Wide.blkTagLe K) hlinB hex).choose, fun _ => Classical.arbitrary A) :=
      ⟨Or.inl ⟨hsucc.1.1, fun hc => hsucc.1.2 (by
          have hc' : b = (exists_ixSucc (Wide.blkTagLe K) hlinB hex).choose := hc
          rw [← hc']
          exact hlinB.1 b)⟩, fun hcc => by
        rcases hcc with ⟨hb2, hne2⟩ | ⟨hb2, -⟩
        · exact hne2 (hlinB.2.2.1 _ _ hb2 hsucc.1.1)
        · exact hsucc.1.2 (by
            have hb2' : (exists_ixSucc (Wide.blkTagLe K) hlinB hex).choose = b := hb2
            rw [hb2']
            exact hlinB.1 b)⟩
    have hs := ixSucc_blkNext A K dd ⟨_, hlt⟩
    obtain ⟨hble, hbne⟩ := blkTag_lt_of_gt_tupTop hs.1
    refine hlinB.2.2.1 _ _ ?_ (hsucc.2 _ ⟨hble, fun hc => hbne (hlinB.2.2.1 _ _ hble hc)⟩)
    -- and it is at most the tag-successor's own first register
    rcases hs.2 _ hlt with ⟨hb3, -⟩ | ⟨hb3, -⟩
    · exact hb3
    · have hb3' : (blkNext A K dd (b, tupTop A dd)).1 =
          (exists_ixSucc (Wide.blkTagLe K) hlinB hex).choose := hb3
      rw [blkNextB, hb3']
      exact hlinB.1 _
  · -- no block above: the sweep stays where it is
    rw [blkNextTag, dif_neg hex]
    have htop : ∀ v : Wide.BlkIx K A dd, Wide.blkLe K A dd v (b, tupTop A dd) := by
      intro v
      rcases hlinB.2.2.2 v.1 b with hb | hb
      · by_cases hEq : v.1 = b
        · exact Or.inr ⟨hEq, tupLeLex_tupTop A dd v.2⟩
        · exact Or.inl ⟨hb, hEq⟩
      · by_cases hEq : v.1 = b
        · exact Or.inr ⟨hEq, tupLeLex_tupTop A dd v.2⟩
        · exact absurd (⟨hb, fun hc => hEq (hlinB.2.2.1 _ _ hc hb)⟩ :
            WMLt (Wide.blkTagLe K) b v.1) (fun hc => hex ⟨v.1, hc⟩)
    exact congrArg Prod.fst (blkNext_of_top A K dd htop)

/-- **A roll-over resets the tuple**: at the last tuple of a block that is not
the last, the next register is the first of the next block, so the pointer's
coordinates all become the least element. -/
theorem blkNext_snd_of_tupTop [Nonempty A] [Nonempty K] {b : Option K}
    (hne : (b, tupTop A dd) ≠ blkTop A K dd) {zero : A} (hbot : ∀ a : A, zero ≤ a)
    (j : Fin dd) : (blkNext A K dd (b, tupTop A dd)).2 j = zero := by
  classical
  have hlin := Wide.isLinOrd_blkLe K A dd
  have hlt : WMLt (Wide.blkLe K A dd) (b, tupTop A dd) (blkTop A K dd) :=
    ⟨blkLe_blkTop A K dd _, fun hc =>
      hne (hlin.2.2.1 _ _ (blkLe_blkTop A K dd _) hc)⟩
  have hs := ixSucc_blkNext A K dd ⟨blkTop A K dd, hlt⟩
  obtain ⟨hble, hbne⟩ := blkTag_lt_of_gt_tupTop hs.1
  -- the first register of the successor's block is between them
  have hgt : WMLt (Wide.blkLe K A dd) (b, tupTop A dd)
      ((blkNext A K dd (b, tupTop A dd)).1, fun _ => zero) :=
    ⟨Or.inl ⟨hble, hbne⟩, fun hcc => by
      rcases hcc with ⟨hb2, hne2⟩ | ⟨hb2, -⟩
      · exact hne2 ((Wide.isLinOrd_blkTagLe K).2.2.1 _ _ hb2 hble)
      · exact hbne hb2.symm⟩
  have hle : Wide.blkLe K A dd
      ((blkNext A K dd (b, tupTop A dd)).1, fun _ => zero)
      (blkNext A K dd (b, tupTop A dd)) :=
    Or.inr ⟨rfl, tupLeLex_const_bot hbot _⟩
  exact congrFun (congrArg Prod.snd (hlin.2.2.1 _ _ (hs.2 _ hgt) hle)) j

/-- **The first register's block is the blockless one**: the layout puts the
registers that stand for no block first, so the least index's block is
`none`. -/
theorem fst_blkBot [Nonempty A] [Nonempty K] : (blkBot A K dd).1 = none := by
  rcases blkLe_blkBot A K dd (none, fun _ => Classical.arbitrary A) with ⟨hb, -⟩ | ⟨hb, -⟩
  · revert hb
    match (blkBot A K dd).1 with
    | none => intro _; rfl
    | some _ => intro hb'; exact absurd hb' not_false
  · exact hb

/-- **The greatest tuple is the greatest element everywhere**: what the sweep's
roll-over test asks about the pointer, coordinate by coordinate. -/
theorem tupTop_apply [Nonempty A] {one : A} (htop : ∀ a : A, a ≤ one)
    (j : Fin dd) : tupTop A dd j = one := by
  have h1 : ∀ u : Lex (Fin dd → A), u ≤ toLex (fun _ : Fin dd => one) :=
    tup_isTop_iff.mpr fun _ a => htop a
  have h2 : toLex (tupTop A dd) ≤ toLex (fun _ : Fin dd => one) := h1 _
  have h3 : toLex (fun _ : Fin dd => one) ≤ toLex (tupTop A dd) :=
    (tupLeLex_iff_toLex_le _ _).mp (tupLeLex_tupTop A dd _)
  have heq : toLex (tupTop A dd) = toLex (fun _ : Fin dd => one) := le_antisymm h2 h3
  exact congrFun (congrArg ofLex heq) j

/-- **A tuple is the greatest exactly when every coordinate is**, which is the
form the roll-over test takes as a formula. -/
theorem eq_tupTop_iff [Nonempty A] {one : A} (htop : ∀ a : A, a ≤ one)
    (t : Fin dd → A) : t = tupTop A dd ↔ ∀ j : Fin dd, t j = one := by
  constructor
  · intro h j
    rw [h]
    exact tupTop_apply htop j
  · intro h
    funext j
    rw [h j, tupTop_apply htop j]

end Advance

namespace PfpData

variable {L : Language.{0, 0}} {dt : PfpData L} {Q : Type} [Fintype Q]
variable [Fintype dt.SlotIx] [DecidableEq dt.SlotIx]

/-! ### The clocked spine -/

omit [DecidableEq dt.SlotIx] in
/-- **The clocked evaluation's spine is definable**: one checkpoint per spine
position, with two rules each – the walk back to the marker, and the dispatch,
which goes into the position's machinery below the last checkpoint and out of
the evaluation at it. There is no third rule, the clocked evaluation running
once and leaving into whatever phase its caller names. -/
theorem uRulesDefinable_nexEvalRule {PM SM B : Type} {nv : ℕ} {ShM : SM → Type}
    {ruleM : ∀ (e : Env L) (s : SM), ShM s →
      Rule e.α Q dt.SlotIx (NexPh B (EvalPh nv PM))}
    {subEntry : Fin nv → PM} {exitPh : NexPh B (EvalPh nv PM)}
    (hM : URulesDefinable ruleM) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.nexEvalRule e.one (ruleM e) subEntry exitPh := by
  rintro (k | s) ρ
  · match ρ with
    | .stay =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩
        (uGDefinable_trkOne (L := L) (Q := Q) (Slot.wk : dt.SlotIx)).not
        (fun _ _ _ => rfl) fun _ _ _ => rfl
    | .dsp =>
      by_cases hk : (k : ℕ) < nv
      · simp only [nexEvalRule, dif_pos hk]
        exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
          uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
          fun _ _ _ => rfl
      · simp only [nexEvalRule, dif_neg hk]
        exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
          uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
          fun _ _ _ => rfl
  · exact hM s ρ

omit [DecidableEq dt.SlotIx] in
/-- **The clocked evaluation's machineries are definable**: the same tower the
space-bounded program runs, one copy per spine position and the output's, at the
clocked program's own phases. -/
theorem uRulesDefinable_nexSmRule {B : Type}
    {args : ∀ (e : Env L) (v : dt.VarIx), dt.VarArgs (A := e.α) (Q := Q) v}
    (h : ∀ v : dt.VarIx, UVarArgsDef v fun e => args e v) :
    URulesDefinable (L := L) (Q := Q) (S := dt.SMF) (Sh := dt.SMSh) fun e =>
      dt.nexSmRule (B := B) e.zero e.one (args e) := by
  rintro (⟨j, s⟩ | s) ρ
  · exact uRulesDefinable_varRuleF
      (emb := fun p => (NexPh.evalP (.sub (Sum.inl ⟨j, p⟩)) :
        NexPh B (EvalPh dt.nv dt.PMF)))
      (exitPh := .evalP (.chk j.succ)) (h (dt.varAt j)) s ρ
  · exact uRulesDefinable_varRuleF
      (emb := fun p => (NexPh.evalP (.sub (Sum.inr p)) :
        NexPh B (EvalPh dt.nv dt.PMF)))
      (exitPh := .acceptP) (h none) s ρ

omit [DecidableEq dt.SlotIx] in
/-- **The clocked evaluation is definable**: its spine over those
machineries. -/
theorem uRulesDefinable_nexEvalRuleF {B : Type}
    {args : ∀ (e : Env L) (v : dt.VarIx), dt.VarArgs (A := e.α) (Q := Q) v}
    (h : ∀ v : dt.VarIx, UVarArgsDef v fun e => args e v) :
    URulesDefinable (L := L) (Q := Q) (S := dt.SEF) (Sh := dt.NexSESh) fun e =>
      dt.nexEvalRuleF (B := B) e.zero e.one (args e) :=
  uRulesDefinable_nexEvalRule (uRulesDefinable_nexSmRule h)


/-! ### The file-laying sweep's own definability

What `USweepSpecDef` asks of `DescriptiveComplexity.Pfp.PfpData.buildSpec`, one
field at a time. The two tests are questions about the pointer's coordinates –
each is the greatest element, or the pointer is at the last register – and the
`st0` reset writes the least element into them. -/

section BuildSpec

variable {A : Type} [LinearOrder A] [Finite A] [Nonempty A]

omit [DecidableEq dt.SlotIx] in
/-- **The roll-over test is definable**: the pointer holds the last tuple
exactly when every coordinate slot holds the greatest element. -/
theorem uGDefinable_ptrTup_eq_tupTop (coord : Fin dt.dd → dt.CtlIx) :
    UGDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
      fun e f _ => dt.ptrTup coord f = tupTop e.α dt.dd :=
  (uGDefinable_forall (R := fun j : Fin dt.dd => fun e f
      (_ : dt.SlotIx → e.α) => f (coord j) = e.one)
    fun j => uGDefinable_ctlOne (L := L) (W := dt.SlotIx) (coord j)).congr
    fun e f _ => eq_tupTop_iff e.htop (dt.ptrTup coord f)

omit [DecidableEq dt.SlotIx] in
/-- **The stop test is definable**: the pointer is at the last register exactly
when its block is the last one – a comparison the formula is built with – and
every coordinate slot holds the greatest element. -/
theorem uGDefinable_done [Nonempty dt.KIx] (coord : Fin dt.dd → dt.CtlIx)
    (b : Option dt.KIx) :
    UGDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
      fun e f _ => ((b, dt.ptrTup coord f) = blkTop e.α dt.KIx dt.dd) :=
  ((uGDefinable_const (Q := dt.CtlIx) (W := dt.SlotIx)
      (b = blkTopB dt.KIx)).and
    (uGDefinable_ptrTup_eq_tupTop coord)).congr fun e f _ => by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rw [← fst_blkTop (A := e.α) (K := dt.KIx) (dd := dt.dd)]
        exact congrArg Prod.fst h
      · exact (congrArg Prod.snd h).trans (snd_blkTop e.α dt.KIx dt.dd)
    · rintro ⟨hb, ht⟩
      refine Prod.ext ?_ ?_
      · rw [hb, ← fst_blkTop (A := e.α) (K := dt.KIx) (dd := dt.dd)]
      · rw [ht, snd_blkTop e.α dt.KIx dt.dd]

omit [DecidableEq dt.SlotIx] in
/-- **The reset to the file's first register is definable**: the coordinate
slots take the least element and every other slot keeps what it held. Which
slots are coordinates is decided when the formula is built. -/
theorem uStDefinable_st0 [Nonempty dt.KIx] (coord : Fin dt.dd → dt.CtlIx) :
    UStDefinable (L := L) (W := dt.SlotIx)
      fun e (f : dt.CtlIx → e.α) (_ : dt.SlotIx → e.α) =>
        dt.ctlOf coord f (blkBot e.α dt.KIx dt.dd).2 := by
  classical
  intro q
  by_cases hq : ∃ j : Fin dt.dd, coord j = q
  · refine (uSlotDefinable_zero (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)).congr
      fun e f _ => ?_
    change dt.ctlOf coord f (blkBot e.α dt.KIx dt.dd).2 q = e.zero
    rw [ctlOf, dif_pos hq]
    exact snd_blkBot_apply e.hbot _
  · refine (uSlotDefinable_ctl (L := L) (W := dt.SlotIx) q).congr fun e f _ => ?_
    change dt.ctlOf coord f (blkBot e.α dt.KIx dt.dd).2 q = f q
    rw [ctlOf, dif_neg hq]

omit [DecidableEq dt.SlotIx] in
/-- **The first-register test is definable**: the pointer is at the file's first
register exactly when its block is the blockless one – decided when the formula
is built – and every coordinate slot holds the least element. -/
theorem uGDefinable_atBot [Nonempty dt.KIx] (coord : Fin dt.dd → dt.CtlIx)
    (b : Option dt.KIx) :
    UGDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
      fun e f _ => ((b, dt.ptrTup coord f) = blkBot e.α dt.KIx dt.dd) :=
  ((uGDefinable_const (Q := dt.CtlIx) (W := dt.SlotIx) (b = none)).and
    (uGDefinable_forall (R := fun j : Fin dt.dd => fun e f
        (_ : dt.SlotIx → e.α) => f (coord j) = e.zero)
      fun j => uGDefinable_ctlZero (L := L) (W := dt.SlotIx)
        (coord j))).congr fun e f _ => by
    constructor
    · intro h
      refine ⟨(congrArg Prod.fst h).trans
        (fst_blkBot (A := e.α) (K := dt.KIx) (dd := dt.dd)), fun j => ?_⟩
      have hj : dt.ptrTup coord f j = (blkBot e.α dt.KIx dt.dd).2 j :=
        congrFun (congrArg Prod.snd h) j
      exact hj.trans (snd_blkBot_apply e.hbot j)
    · rintro ⟨hb, ht⟩
      refine Prod.ext ?_ (funext fun j => ?_)
      · rw [hb, fst_blkBot (A := e.α) (K := dt.KIx) (dd := dt.dd)]
      · change f (coord j) = (blkBot e.α dt.KIx dt.dd).2 j
        rw [ht j, snd_blkBot_apply e.hbot j]

omit [DecidableEq dt.SlotIx] in
/-- **What the file-laying sweep writes is definable**: the register mark and
its two ends, the block one-hot, the name slots the pointer holds, the padding
test, and the blank in every track the file does not carry. Every one of them is
a slot of the control or a designated element, which is what makes the sweep a
*definable* write. -/
theorem uTrDefinable_buildWr [Nonempty dt.KIx] (coord : Fin dt.dd → dt.CtlIx)
    (b : Option dt.KIx) :
    UTrDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
      fun e f _ => dt.buildWr e.zero e.one coord b f := by
  intro sl
  match sl with
  | .reg => exact uSlotDefinable_one (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
  | .regFirst => exact uSlotDefinable_bitVal (uGDefinable_atBot coord b)
  | .regLast => exact uSlotDefinable_bitVal (uGDefinable_done coord b)
  | .blk c =>
    exact uSlotDefinable_bitVal
      (uGDefinable_const (Q := dt.CtlIx) (W := dt.SlotIx) (b = c))
  | .name j =>
    exact uSlotDefinable_ctl (L := L) (W := dt.SlotIx)
      (coord (Fin.castLE dt.dd0Le j))
  | .pdd =>
    exact uSlotDefinable_bitVal
      (uGDefinable_forall (R := fun j : Fin dt.dd => fun e f (_ : dt.SlotIx → e.α) =>
          dt.dd0 ≤ (j : ℕ) → f (coord j) = e.zero)
        fun j => (uGDefinable_const (Q := dt.CtlIx) (W := dt.SlotIx)
          (dt.dd0 ≤ (j : ℕ))).imp
          (uGDefinable_ctlZero (L := L) (W := dt.SlotIx) (coord j)))
  | .mir => exact uSlotDefinable_zero (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
  | .tgt => exact uSlotDefinable_zero (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
  | .sav => exact uSlotDefinable_zero (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
  | .val => exact uSlotDefinable_zero (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
  | .wk => exact uSlotDefinable_zero (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
  | .bot => exact uSlotDefinable_zero (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
  | .ltp => exact uSlotDefinable_zero (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
  | .old _ => exact uSlotDefinable_zero (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
  | .new _ => exact uSlotDefinable_zero (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)

omit [DecidableEq dt.SlotIx] in
/-- **The pointer's next tuple is definable, coordinate by coordinate**: which
coordinate rolls over is a question about *which coordinates are maximal*, and
the value at it is the order's own successor. This is
`DescriptiveComplexity.Pfp.PfpData.uSlotDefinable_tupNext_lvC` at the sweep's
own coordinates. -/
theorem uSlotDefinable_tupNext_coord (coord : Fin dt.dd → dt.CtlIx) (j : Fin dt.dd) :
    USlotDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
      fun _ f _ => tupNext (dt.ptrTup coord f) j := by
  refine uSlotDefinable_cases
    (R := fun p : Fin dt.dd => fun e (f : dt.CtlIx → e.α) (_ : dt.SlotIx → e.α) =>
      f (coord p) ≠ e.one ∧ ∀ j' : Fin dt.dd, p < j' → f (coord j') = e.one)
    (U := fun p : Fin dt.dd => fun e (f : dt.CtlIx → e.α) (_ : dt.SlotIx → e.α) =>
      if j < p then f (coord j) else if j = p then ordSucc (f (coord j)) else e.zero)
    (V' := fun _ f _ => f (coord j))
    (fun p => (uGDefinable_ctlOne (L := L) (W := dt.SlotIx) (coord p)).not.and
      (uGDefinable_forall fun j' : Fin dt.dd =>
        (uGDefinable_const (p < j')).imp
          (uGDefinable_ctlOne (L := L) (W := dt.SlotIx) (coord j'))))
    (fun _ => ((uSlotDefinable_ctl (L := L) (W := dt.SlotIx) (coord j)).ite
      ((uSlotDefinable_ctlSucc (L := L) (W := dt.SlotIx) (coord j)).ite
        uSlotDefinable_zero)))
    (uSlotDefinable_ctl (L := L) (W := dt.SlotIx) (coord j)) ?_ ?_
  · rintro e f g p ⟨hp, hab⟩
    refine tupNext_apply_of_carry e.hbot (t := dt.ptrTup coord f) (p := p) ?_ ?_ j
    · exact fun hc => hp (le_antisymm (e.htop _) (hc e.one))
    · intro j' hj'
      have hj1 : dt.ptrTup coord f j' = e.one := hab j' hj'
      rw [hj1]
      exact e.htop
  · intro e f g hno
    have hmax : IsMaxTup (dt.ptrTup coord f) := by
      by_contra hc
      obtain ⟨p, hp, hab⟩ := exists_carry e.htop hc
      exact hno p ⟨hp, hab⟩
    rw [tupNext_of_isMaxTup hmax]
    rfl

omit [DecidableEq dt.SlotIx] in
/-- **The sweep's advance is definable**: at a coordinate slot the pointer takes
the next register's own tuple – the lexicographic successor within a block, the
least element at a roll-over – and every other slot keeps what it held. This is
the one write of the whole program that is not a copy. -/
theorem uStDefinable_ptrNext [Nonempty dt.KIx] {coord : Fin dt.dd → dt.CtlIx}
    (hcoord : Function.Injective coord) (b : Option dt.KIx) :
    UStDefinable (L := L) (W := dt.SlotIx)
      fun e (f : dt.CtlIx → e.α) (_ : dt.SlotIx → e.α) => dt.ptrNext coord b f := by
  classical
  intro q
  by_cases hq : ∃ j : Fin dt.dd, coord j = q
  · obtain ⟨j, rfl⟩ := hq
    -- at a coordinate the new value is the next register's tuple there
    have hval : ∀ (e : Env L) (f : dt.CtlIx → e.α),
        dt.ptrNext coord b f (coord j) =
          (blkNext e.α dt.KIx dt.dd (b, dt.ptrTup coord f)).2 j := by
      intro e f
      have hex : ∃ j' : Fin dt.dd, coord j' = coord j := ⟨j, rfl⟩
      change (if h : ∃ j' : Fin dt.dd, coord j' = coord j then
        (blkNext e.α dt.KIx dt.dd (b, dt.ptrTup coord f)).2 h.choose else f (coord j)) = _
      rw [dif_pos hex, hcoord hex.choose_spec]
    by_cases hb : b = blkTopB dt.KIx
    · -- the last block: the advance is the tuple's successor, itself at the top
      refine (uSlotDefinable_tupNext_coord coord j).congr fun e f _ => ?_
      change dt.ptrNext coord b f (coord j) = tupNext (dt.ptrTup coord f) j
      rw [hval e f]
      by_cases ht : dt.ptrTup coord f = tupTop e.α dt.dd
      · have htop : (b, dt.ptrTup coord f) = blkTop e.α dt.KIx dt.dd := by
          refine Prod.ext ?_ ?_
          · rw [hb, ← fst_blkTop (A := e.α) (K := dt.KIx) (dd := dt.dd)]
          · rw [ht, snd_blkTop e.α dt.KIx dt.dd]
        have hmax : ∀ v : Wide.BlkIx dt.KIx e.α dt.dd,
            Wide.blkLe dt.KIx e.α dt.dd v (b, dt.ptrTup coord f) := by
          intro v
          rw [htop]
          exact blkLe_blkTop e.α dt.KIx dt.dd v
        have hmt : IsMaxTup (dt.ptrTup coord f) := by
          intro p a
          rw [ht, tupTop_apply e.htop]
          exact e.htop a
        rw [blkNext_of_top e.α dt.KIx dt.dd hmax, tupNext_of_isMaxTup hmt]
      · rw [blkNext_snd_of_ne_tupTop ht]
    · -- any other block: at the top of it the pointer resets
      refine uSlotDefinable_cases
        (R := fun _ : Unit => fun e (f : dt.CtlIx → e.α) (_ : dt.SlotIx → e.α) =>
          dt.ptrTup coord f = tupTop e.α dt.dd)
        (U := fun _ : Unit => fun e (_ : dt.CtlIx → e.α) (_ : dt.SlotIx → e.α) => e.zero)
        (V' := fun e f _ => tupNext (dt.ptrTup coord f) j)
        (fun _ => uGDefinable_ptrTup_eq_tupTop coord)
        (fun _ => uSlotDefinable_zero) (uSlotDefinable_tupNext_coord coord j)
        ?_ ?_
      · rintro e f g - ht
        change dt.ptrNext coord b f (coord j) = e.zero
        rw [hval e f, ht]
        refine blkNext_snd_of_tupTop (fun hc => hb ?_) e.hbot j
        rw [← fst_blkTop (A := e.α) (K := dt.KIx) (dd := dt.dd)]
        exact congrArg Prod.fst hc
      · intro e f g hno
        change dt.ptrNext coord b f (coord j) = tupNext (dt.ptrTup coord f) j
        rw [hval e f, blkNext_snd_of_ne_tupTop (hno ())]
  · refine (uSlotDefinable_ctl (L := L) (W := dt.SlotIx) q).congr fun e f _ => ?_
    change dt.ptrNext coord b f q = f q
    rw [ptrNext, dif_neg hq]

end BuildSpec

/-! ### The outer layer

A clocked program's two sweeps are *specifications* rather than kits: what they
write at a cell, where they leave the pointer, and when they are over are the
caller's, so their definability is the caller's too. These are the two bundles,
and everything else in the outer layer – the opening step, the approach, the two
walks home and their exits, the guess's stop – is a constant rule with a guard
the toolkit already has. -/

/-- **What makes a file-laying sweep definable**: its write, its three pointers
and its two tests. The next block is a function of the phase alone, so nothing
is asked of it. -/
structure USweepSpecDef {B : Type} (β : ∀ e : Env L, SweepSpec e.α Q dt.SlotIx B) :
    Prop where
  /-- The tracks it leaves at the cell. -/
  wr : ∀ b : B, UTrDefinable fun e => (β e).wr b
  /-- The pointer it leaves within a block. -/
  st : ∀ b : B, UStDefinable fun e => (β e).st b
  /-- The pointer the exit resets to the file's first register. -/
  st0 : UStDefinable fun e => (β e).st0
  /-- The pointer it leaves at a roll-over. -/
  stRoll : ∀ b : B, UStDefinable fun e => (β e).stRoll b
  /-- The next block is chosen when the formula is built, not at the
  instance. -/
  nx : ∀ b : B, ∃ b' : B, ∀ e : Env L, (β e).nx b = b'
  /-- The roll-over test. -/
  roll : ∀ b : B, UGDefinable fun e f (_ : dt.SlotIx → e.α) => (β e).Roll b f
  /-- The stop test. -/
  done : ∀ b : B, UGDefinable fun e f (_ : dt.SlotIx → e.α) => (β e).Done b f

/-- **And what makes a guessing sweep definable**: the same, at each value it
may guess. -/
structure UGuessSpecDef {B G : Type}
    (γ : ∀ e : Env L, GuessSpec e.α Q dt.SlotIx B G) : Prop where
  /-- The tracks it leaves at the cell, at this value. -/
  wr : ∀ (b : B) (x : G), UTrDefinable fun e => (γ e).wr b x
  /-- The pointer it leaves, at this value. -/
  st : ∀ (b : B) (x : G), UStDefinable fun e => (γ e).st b x
  /-- The pointer it leaves at a roll-over. -/
  stRoll : ∀ (b : B) (x : G), UStDefinable fun e => (γ e).stRoll b x
  /-- The next block is chosen when the formula is built. -/
  nx : ∀ b : B, ∃ b' : B, ∀ e : Env L, (γ e).nx b = b'
  /-- The roll-over test. -/
  roll : ∀ b : B, UGDefinable fun e f (_ : dt.SlotIx → e.α) => (γ e).Roll b f
  /-- The stop test. -/
  done : ∀ b : B, UGDefinable fun e f (_ : dt.SlotIx → e.α) => (γ e).Done b f

omit [DecidableEq dt.SlotIx] in
/-- **The file-laying sweep is definable**, field by field: what it writes is
the file's background at the register the pointer names, where it leaves the
pointer is the next register's tuple, its exit resets to the file's first
register, and its two tests ask whether the pointer is at the last tuple and at
the last register. The next block is a function of the phase, so it is chosen
when the formula is built. -/
theorem uSweepSpecDef_buildSpec [Nonempty dt.KIx] {coord : Fin dt.dd → dt.CtlIx}
    (hcoord : Function.Injective coord) :
    USweepSpecDef (L := L) (Q := dt.CtlIx) (dt := dt)
      fun e => dt.buildSpec e.zero e.one coord where
  wr b := uTrDefinable_buildWr coord b
  st b := uStDefinable_ptrNext hcoord b
  st0 := uStDefinable_st0 coord
  stRoll b := uStDefinable_ptrNext hcoord b
  nx b := ⟨blkNextTag dt.KIx b, fun e => blkNextB_eq (A := e.α) b⟩
  roll _ := uGDefinable_ptrTup_eq_tupTop coord
  done b := uGDefinable_done coord b

omit [DecidableEq dt.SlotIx] in
/-- **The sweep that does nothing is definable**: every field is the identity or
a constant, and its two tests are `True` – which is what makes the phase a single
step. This is the specification a program that is *handed* its file puts where a
file-laying one puts `uSweepSpecDef_buildSpec`. -/
theorem uSweepSpecDef_nullSpec {B : Type} :
    USweepSpecDef (L := L) (Q := dt.CtlIx) (dt := dt)
      fun e => dt.nullSpec (A := e.α) B where
  wr _ := uTrDefinable_id
  st _ := uStDefinable_id
  st0 := uStDefinable_id
  stRoll _ := uStDefinable_id
  nx b := ⟨b, fun _ => rfl⟩
  roll _ := uGDefinable_true
  done _ := uGDefinable_true

omit [DecidableEq dt.SlotIx] in
/-- **What the guessing sweep writes is definable**: the stage tracks take the
guessed bit – a designated element, chosen when the formula is built, since the
value guessed is the rule's own shape – and every other slot keeps what it
held. -/
theorem uTrDefinable_guessWr (x : dt.d.B.ι → Bool) :
    UTrDefinable (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
      fun e _ g => dt.guessWr e.zero e.one x g := by
  intro sl
  match sl with
  | .old i =>
    exact uSlotDefinable_bitVal
      (uGDefinable_const (Q := dt.CtlIx) (W := dt.SlotIx) (x i = true))
  | .reg => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.reg
  | .regFirst => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.regFirst
  | .regLast => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.regLast
  | .blk c => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) (Slot.blk c)
  | .name j => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) (Slot.name j)
  | .pdd => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.pdd
  | .mir => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.mir
  | .tgt => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.tgt
  | .sav => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.sav
  | .val => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.val
  | .wk => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.wk
  | .bot => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.bot
  | .ltp => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) Slot.ltp
  | .new i => exact uSlotDefinable_trk (L := L) (Q := dt.CtlIx) (Slot.new i)

omit [DecidableEq dt.SlotIx] in
/-- **The guessing sweep is definable**: it writes the guessed bit and moves no
pointer, so every field but the write is the identity or a constant. Its stop is
not a test at all – the sweep stops nondeterministically, which is why `Roll` is
always true and `Done` never. -/
theorem uGuessSpecDef_regionSpec :
    UGuessSpecDef (L := L) (Q := dt.CtlIx) (dt := dt)
      fun e => dt.regionSpec e.zero e.one where
  wr _ x := uTrDefinable_guessWr x
  st _ _ := uStDefinable_id (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
  stRoll _ _ := uStDefinable_id (L := L) (Q := dt.CtlIx) (W := dt.SlotIx)
  nx b := ⟨b, fun _ => rfl⟩
  roll _ := uGDefinable_true
  done _ := uGDefinable_false

/-- **The clocked program's outer layer is definable**: the opening step that
plants the two marks, the approach walk and its stop, the file-laying sweep at
its specification, the walk home and its turn, the guessing sweep at its own
specification and its stop, the second walk home, and the evaluation's rules as
the parameter. -/
theorem uRulesDefinable_nexRule {PE SE B G : Type} {ShE : SE → Type}
    {β : ∀ e : Env L, SweepSpec e.α Q dt.SlotIx B}
    {γ : ∀ e : Env L, GuessSpec e.α Q dt.SlotIx B G}
    {ruleE : ∀ (e : Env L) (s : SE), ShE s → Rule e.α Q dt.SlotIx (NexPh B PE)}
    {evalEntry : PE} {bot : B}
    (hβ : USweepSpecDef β) (hγ : UGuessSpecDef γ) (hE : URulesDefinable ruleE) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.nexRule e.one (β e) (γ e) (ruleE e) evalEntry bot := by
  rintro (- | - | - | - | - | - | - | s) ρ
  · exact uRuleDefinable_of_keepSt ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
      uRight_of_true fun _ => trivial⟩ uGDefinable_true (fun _ _ _ => rfl)
      ((uTrDefinable_id.update Slot.wk uSlotDefinable_one).update Slot.bot
        uSlotDefinable_one)
  · match ρ with
    | Sum.inl _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_true (fun _ _ _ => rfl)
        fun _ _ _ => rfl
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_true (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl b =>
      exact ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial, (hβ.roll b).not, hβ.st b, hβ.wr b⟩
    | Sum.inr (Sum.inl b) =>
      obtain ⟨b', hb'⟩ := hβ.nx b
      exact ⟨⟨_, fun _ => rfl⟩, ⟨NexPh.buildP b', fun e => by
          change NexPh.buildP ((β e).nx b) = NexPh.buildP b'
          rw [hb']⟩,
        uRight_of_true fun _ => trivial, (hβ.roll b).and (hβ.done b).not,
        hβ.stRoll b, hβ.wr b⟩
    | Sum.inr (Sum.inr (Sum.inl b)) =>
      exact ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial, (hβ.roll b).and (hβ.done b),
        hβ.stRoll b, hβ.wr b⟩
    | Sum.inr (Sum.inr (Sum.inr _)) =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ uGDefinable_true (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact HomeKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keepWr ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG hβ.st0
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl ⟨b, x⟩ =>
      exact ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial, (hγ.roll b).not, hγ.st b x, hγ.wr b x⟩
    | Sum.inr (Sum.inl ⟨b, x⟩) =>
      obtain ⟨b', hb'⟩ := hγ.nx b
      exact ⟨⟨_, fun _ => rfl⟩, ⟨NexPh.guessP b', fun e => by
          change NexPh.guessP ((γ e).nx b) = NexPh.guessP b'
          rw [hb']⟩,
        uRight_of_true fun _ => trivial, (hγ.roll b).and (hγ.done b).not,
        hγ.stRoll b x, hγ.wr b x⟩
    | Sum.inr (Sum.inr (Sum.inl ⟨b, x⟩)) =>
      exact ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial, (hγ.roll b).and (hγ.done b),
        hγ.stRoll b x, hγ.wr b x⟩
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ uGDefinable_true (fun _ _ _ => rfl)
        fun _ _ _ => rfl
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_false fun _ => not_false⟩ uGDefinable_true (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · match ρ with
    | Sum.inl σ => exact HomeKit.uRuleDefinable σ
    | Sum.inr _ =>
      exact uRuleDefinable_of_keep ⟨⟨_, fun _ => rfl⟩, ⟨_, fun _ => rfl⟩,
        uRight_of_true fun _ => trivial⟩ uGDefinable_exitG (fun _ _ _ => rfl)
        fun _ _ _ => rfl
  · exact ρ.elim
  · exact hE s ρ

/-- **The clocked program's whole rule set is definable**: the outer layer
around the evaluation, at any two sweep specifications that are themselves
definable. -/
theorem uRulesDefinable_nexProgRule {B G : Type}
    {β : ∀ e : Env L, SweepSpec e.α Q dt.SlotIx B}
    {γ : ∀ e : Env L, GuessSpec e.α Q dt.SlotIx B G}
    {args : ∀ (e : Env L) (v : dt.VarIx), dt.VarArgs (A := e.α) (Q := Q) v}
    {bot : B}
    (hβ : USweepSpecDef β) (hγ : UGuessSpecDef γ)
    (h : ∀ v : dt.VarIx, UVarArgsDef v fun e => args e v) :
    URulesDefinable (L := L) (Q := Q) fun e =>
      dt.nexRule e.one (β e) (γ e) (dt.nexEvalRuleF (B := B) e.zero e.one (args e))
        (.chk 0) bot :=
  uRulesDefinable_nexRule hβ hγ (uRulesDefinable_nexEvalRuleF h)

/-- **The clocked program's own rule set is definable**: the two sweeps it
actually runs, the tower it shares with the space-bounded program, and the outer
layer around them. This is what a reduction emitting the clocked machine has to
hand `DescriptiveComplexity.Pfp.PfpData.reads_progFrom`; what is left to it is
its own `VarArgs`, which is the same obligation the space-bounded reduction
already meets. -/
theorem uRulesDefinable_nexProg [Nonempty dt.KIx]
    {coord : Fin dt.dd → dt.CtlIx} (hcoord : Function.Injective coord)
    {args : ∀ (e : Env L) (v : dt.VarIx),
      dt.VarArgs (A := e.α) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx}
    (h : ∀ v : dt.VarIx, UVarArgsDef v fun e => args e v) :
    URulesDefinable (L := L) (Q := dt.CtlIx) fun e =>
      dt.nexRule e.one (dt.buildSpec e.zero e.one coord) (dt.regionSpec e.zero e.one)
        (dt.nexEvalRuleF (B := Option dt.KIx) e.zero e.one (args e)) (.chk 0) bot :=
  uRulesDefinable_nexProgRule (uSweepSpecDef_buildSpec hcoord)
    uGuessSpecDef_regionSpec h

/-- **The rule set of a clocked program that is *handed* its file is definable,
and needs no coordinate map**: the sweep that would have laid the file is
`nullSpec`, whose definability is free, so nothing in the program asks for an
injective `Fin dd → CtlIx` – which is the map no wide machine's control can hold
(`DescriptiveComplexity.Pfp.card_ctl_lt_card_univ`). This is the rule set a
reduction into `DescriptiveComplexity.WideRegAccept` emits. -/
theorem uRulesDefinable_nexProgHanded
    {args : ∀ (e : Env L) (v : dt.VarIx),
      dt.VarArgs (A := e.α) (Q := dt.CtlIx) v}
    {bot : Option dt.KIx}
    (h : ∀ v : dt.VarIx, UVarArgsDef v fun e => args e v) :
    URulesDefinable (L := L) (Q := dt.CtlIx) fun e =>
      dt.nexRule e.one (dt.nullSpec (A := e.α) (Option dt.KIx))
        (dt.regionSpec e.zero e.one)
        (dt.nexEvalRuleF (B := Option dt.KIx) e.zero e.one (args e)) (.chk 0) bot :=
  uRulesDefinable_nexProgRule uSweepSpecDef_nullSpec uGuessSpecDef_regionSpec h

omit [DecidableEq dt.SlotIx] in
/-- **The clocked program's accepting predicate is definable**: the phase is
decided when the formula is built, and the bit it conjoins is the outermost
variable's verdict – the same field the space-bounded program accepts on. -/
theorem uGDefinable_nexAccept {B PE : Type}
    {args : ∀ (e : Env L) (v : dt.VarIx),
      dt.VarArgs (A := e.α) (Q := dt.CtlIx) v}
    (h : UVarArgsDef (Q := dt.CtlIx) none fun e => args e none)
    (p : NexPh B PE) :
    UGDefinable (L := L) (W := dt.SlotIx) fun e f _ =>
      p = NexPh.acceptP ∧ (args e none).accBit f :=
  (uGDefinable_const (p = NexPh.acceptP)).and h.accBit

end PfpData

end Pfp

end DescriptiveComplexity
