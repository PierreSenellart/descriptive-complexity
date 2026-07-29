/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.InductiveCounting.Order

/-!
# Soundness of the inductive-counting machine

Every accepting run of `DescriptiveComplexity.InductiveCounting.CfgStep` proves what it claims:
no target is reachable from a source. The proof is a phase-indexed invariant,
`DescriptiveComplexity.InductiveCounting.Inv`, preserved by every transition.

The delicate part is the inner loop, where the machine *guesses* which nodes
belong to the current layer. A guess is certified, so the guessed set is always
a subset of the layer; what rules out a guess that is too *small* is the count:
the invariant records that the counter is at most the number of layer nodes
already scanned, and that it is *strictly* below that number as soon as a node
that would have mattered – a target, or a node putting the outer node into the
next layer – has been skipped
(`DescriptiveComplexity.InductiveCounting.InnerInv`, last clause). At the end of the scan the
counter is checked against `|Rset d|`, which leaves no room for a skipped node.
-/

namespace DescriptiveComplexity

namespace InductiveCounting

section Sound

variable {V : Type} [LinearOrder V] [Finite V] (E : V → V → Prop) (S T : V → Prop)

/-! ### Reading a configuration -/

/-- The layer index recorded by the stage register. -/
noncomputable def stage (s : Cfg V) : ℕ := orank (s.regs Reg.d)

/-- A node `y` witnessing that the outer register's node lies in the next
layer: it is that node, or has an edge to it. -/
def Wit (r : WithBot V) (y : V) : Prop := (↑y : WithBot V) = r ∨ EW E ↑y r

variable {E S T}

omit [LinearOrder V] [Finite V] in
@[simp] theorem eW_coe_coe {p q : V} : EW E ↑p ↑q ↔ E p q := by
  constructor
  · rintro ⟨p', q', hp, hq, h⟩
    exact (WithBot.coe_inj.mp hp) ▸ (WithBot.coe_inj.mp hq) ▸ h
  · exact fun h => ⟨p, q, rfl, rfl, h⟩

omit [LinearOrder V] [Finite V] in
@[simp] theorem pW_coe {p : V} : PW S ↑p ↔ S p := by
  constructor
  · rintro ⟨p', hp, h⟩
    exact (WithBot.coe_inj.mp hp) ▸ h
  · exact fun h => ⟨p, rfl, h⟩

omit [LinearOrder V] [Finite V] in
/-- The next layer is exactly the nodes witnessed by the current one. -/
theorem mem_rset_succ_iff_wit {d : ℕ} {vv : V} :
    vv ∈ Rset E S (d + 1) ↔ ∃ y ∈ Rset E S d, Wit E (↑vv : WithBot V) y := by
  rw [mem_rset_succ]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  rw [Wit]
  simp only [eW_coe_coe, WithBot.coe_inj]

/-! ### The invariant -/

variable (E S T)

/-- The invariant of the inner loop, relative to the set `P` of nodes already
scanned by it: the stage count is exact, the outer count is exact for the part
of the next layer already scanned, and the inner count is at most – and, as
soon as something was skipped that should not have been, strictly below – the
number of layer nodes scanned. -/
def InnerInv (s : Cfg V) (P : Set V) : Prop :=
  (∃ vv : V, s.regs Reg.v = ↑vv) ∧
    orank (s.regs Reg.c) = (Rset E S (stage s)).ncard ∧
    orank (s.regs Reg.c2) =
      (Rset E S (stage s + 1) ∩ predSet (s.regs Reg.v)).ncard ∧
    orank (s.regs Reg.cnt) ≤ (Rset E S (stage s) ∩ P).ncard ∧
    (s.flag = true → ∃ vv : V, s.regs Reg.v = ↑vv ∧ vv ∈ Rset E S (stage s + 1)) ∧
    (∀ y ∈ Rset E S (stage s) ∩ P,
      (T y ∨ (s.flag = false ∧ Wit E (s.regs Reg.v) y)) →
        orank (s.regs Reg.cnt) < (Rset E S (stage s) ∩ P).ncard)

/-- The invariant, phase by phase. -/
def PhaseInv (ph : Phase) (s : Cfg V) : Prop :=
  match ph with
  | .initCount =>
      (∃ vv : V, s.regs Reg.v = ↑vv) ∧
        orank (s.regs Reg.c) = ({x | S x} ∩ predSet (s.regs Reg.v)).ncard
  | .inner => InnerInv E S T s (predSet (s.regs Reg.u)) ∧ ∃ uu : V, s.regs Reg.u = ↑uu
  | .walk =>
      InnerInv E S T s (predSet (s.regs Reg.u)) ∧
        orank (s.regs Reg.j) ≤ stage s ∧
        ∃ ww uu : V, s.regs Reg.w = ↑ww ∧ s.regs Reg.u = ↑uu ∧
          RInLe E (stage s - orank (s.regs Reg.j)) ww uu ∧ ¬T uu
  | .certDone =>
      InnerInv E S T s (predSet (s.regs Reg.u)) ∧
        ∃ uu : V, s.regs Reg.u = ↑uu ∧ uu ∈ Rset E S (stage s) ∧ ¬T uu
  | .check => InnerInv E S T s Set.univ
  | .stageEnd =>
      orank (s.regs Reg.c) = (Rset E S (stage s)).ncard ∧
        orank (s.regs Reg.c2) = (Rset E S (stage s + 1)).ncard ∧
        ∀ y ∈ Rset E S (stage s), ¬T y
  | .accept => ¬∃ a b : V, S a ∧ T b ∧ Relation.ReflTransGen E a b

/-- The invariant of a configuration. -/
def Inv (s : Cfg V) : Prop := PhaseInv E S T s.phase s

/-! ### Two steps of the inner loop -/

variable {E S T}

/-- Scanning one more node without certifying it. -/
theorem innerInv_skip {s s' : Cfg V} {uu : V} {P : Set V}
    (hinv : InnerInv E S T s P) (huP : uu ∉ P)
    (hstage : stage s' = stage s)
    (hc : s'.regs Reg.c = s.regs Reg.c) (hc2 : s'.regs Reg.c2 = s.regs Reg.c2)
    (hv : s'.regs Reg.v = s.regs Reg.v) (hcnt : s'.regs Reg.cnt = s.regs Reg.cnt)
    (hflag : s'.flag = s.flag) :
    InnerInv E S T s' (insert uu P) := by
  obtain ⟨hvnode, hcv, hc2v, hcntv, hflagv, hdef⟩ := hinv
  have hle : (Rset E S (stage s) ∩ P).ncard ≤ (Rset E S (stage s) ∩ insert uu P).ncard :=
    ncard_inter_insert_le
  refine ⟨hv ▸ hvnode, by rw [hc, hstage, hcv], by rw [hc2, hstage, hv, hc2v], ?_, ?_, ?_⟩
  · rw [hcnt, hstage]
    omega
  · rw [hflag, hv, hstage]
    exact hflagv
  · intro y hy hcond
    rw [hstage] at hy ⊢
    rw [hcnt]
    rw [hflag, hv] at hcond
    rcases hy with ⟨hyR, hyP⟩
    rcases Set.mem_insert_iff.mp hyP with heq | hyP'
    · subst heq
      rw [ncard_inter_insert_of_mem huP hyR]
      omega
    · have := hdef y ⟨hyR, hyP'⟩ hcond
      omega

/-- Scanning one more node and certifying it: the count goes up, and the flag
goes up exactly when the node witnesses the outer node. -/
theorem innerInv_certify {s s' : Cfg V} {uu : V} {P : Set V}
    (hinv : InnerInv E S T s P) (huP : uu ∉ P)
    (huR : uu ∈ Rset E S (stage s)) (huT : ¬T uu)
    (hstage : stage s' = stage s)
    (hc : s'.regs Reg.c = s.regs Reg.c) (hc2 : s'.regs Reg.c2 = s.regs Reg.c2)
    (hv : s'.regs Reg.v = s.regs Reg.v)
    (hcnt : s.regs Reg.cnt ⋖ s'.regs Reg.cnt)
    (hflag : (Wit E (s.regs Reg.v) uu ∧ s'.flag = true) ∨
      (¬Wit E (s.regs Reg.v) uu ∧ s'.flag = s.flag)) :
    InnerInv E S T s' (insert uu P) := by
  obtain ⟨hvnode, hcv, hc2v, hcntv, hflagv, hdef⟩ := hinv
  have hkey : (Rset E S (stage s) ∩ insert uu P).ncard = (Rset E S (stage s) ∩ P).ncard + 1 :=
    ncard_inter_insert_of_mem huP huR
  have hcnt' : orank (s'.regs Reg.cnt) = orank (s.regs Reg.cnt) + 1 := orank_covBy hcnt
  refine ⟨hv ▸ hvnode, by rw [hc, hstage, hcv], by rw [hc2, hstage, hv, hc2v], ?_, ?_, ?_⟩
  · rw [hstage, hkey, hcnt']
    omega
  · intro htrue
    rw [hv, hstage]
    rcases hflag with ⟨hwit, -⟩ | ⟨-, hfl⟩
    · obtain ⟨vv, hvv⟩ := hvnode
      refine ⟨vv, hvv, ?_⟩
      rw [hvv] at hwit
      exact mem_rset_succ_iff_wit.mpr ⟨uu, huR, hwit⟩
    · exact hflagv (by rw [← hfl]; exact htrue)
  · intro y hy hcond
    rw [hstage] at hy ⊢
    rw [hkey, hcnt']
    rw [hv] at hcond
    rcases hy with ⟨hyR, hyP⟩
    have hyP' : y ∈ P := by
      rcases Set.mem_insert_iff.mp hyP with heq | h
      · subst heq
        exfalso
        rcases hcond with hT | ⟨hfl, hwit⟩
        · exact huT hT
        · rcases hflag with ⟨-, htrue⟩ | ⟨hnwit, -⟩
          · rw [htrue] at hfl; exact Bool.noConfusion hfl
          · exact hnwit hwit
      · exact h
    have hcond' : T y ∨ (s.flag = false ∧ Wit E (s.regs Reg.v) y) := by
      rcases hcond with hT | ⟨hfl, hwit⟩
      · exact Or.inl hT
      · refine Or.inr ⟨?_, hwit⟩
        rcases hflag with ⟨-, htrue⟩ | ⟨-, heq⟩
        · rw [htrue] at hfl; exact Bool.noConfusion hfl
        · rw [← heq]; exact hfl
    have := hdef y ⟨hyR, hyP'⟩ hcond'
    omega


/-! ### Preservation, phase by phase -/

omit [Finite V] in
/-- The inner invariant only reads the registers named here. -/
theorem innerInv_congr {s s' : Cfg V} {P : Set V} (hinv : InnerInv E S T s P)
    (hstage : stage s' = stage s) (hc : s'.regs Reg.c = s.regs Reg.c)
    (hc2 : s'.regs Reg.c2 = s.regs Reg.c2) (hv : s'.regs Reg.v = s.regs Reg.v)
    (hcnt : s'.regs Reg.cnt = s.regs Reg.cnt) (hflag : s'.flag = s.flag) :
    InnerInv E S T s' P := by
  obtain ⟨hvnode, hcv, hc2v, hcntv, hflagv, hdef⟩ := hinv
  exact ⟨hv ▸ hvnode, by rw [hc, hstage, hcv], by rw [hc2, hstage, hv, hc2v],
    by rw [hcnt, hstage]; exact hcntv, by rw [hflag, hv, hstage]; exact hflagv,
    by rw [hcnt, hstage, hflag, hv]; exact hdef⟩

/-- Counting the sources, one node at a time. -/
theorem inv_step_initCount {s s' : Cfg V} (hp : s.phase = Phase.initCount)
    (hinv : Inv E S T s) (hstep : CfgStep E S T s s') : Inv E S T s' := by
  obtain ⟨l, hl, hsat⟩ := hstep
  have hinv' : PhaseInv E S T Phase.initCount s := hp ▸ hinv
  obtain ⟨⟨vv, hvv⟩, hcv⟩ := hinv'
  rw [hvv] at hcv
  change PhaseInv E S T s'.phase s'
  rw [hp] at hl
  cases hq : s'.phase <;> rw [hq] at hl <;> simp only [table] at hl
  -- scanning on
  · split_ifs at hl with hflag
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;>
        simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
      · obtain ⟨hsrc, hcc, hvcov⟩ := hsat
        rw [hvv] at hsrc hvcov
        obtain ⟨vv', hvv', -⟩ := exists_coe_of_covBy hvcov
        refine ⟨⟨vv', hvv'⟩, ?_⟩
        rw [ncard_inter_predSet_covBy_of_mem (P := {x | S x}) hvcov (pW_coe.mp hsrc), ← hcv,
          ← orank_covBy hcc]
      · obtain ⟨hnsrc, hcc, hvcov⟩ := hsat
        rw [hvv] at hnsrc hvcov
        obtain ⟨vv', hvv', -⟩ := exists_coe_of_covBy hvcov
        refine ⟨⟨vv', hvv'⟩, ?_⟩
        rw [ncard_inter_predSet_covBy_of_notMem (P := {x | S x}) hvcov
          (fun h => hnsrc (pW_coe.mpr h)), ← hcv, hcc]
    · exact absurd hl List.not_mem_nil
  -- the scan is over: the first stage begins
  · split_ifs at hl with hflag
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;>
        simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
      · obtain ⟨hsrc, hcc, htop, hd0, hc20, hcnt0, hvmin, humin⟩ := hsat
        rw [hvv] at hsrc htop
        obtain ⟨vv', hvv', hvv'min⟩ := hvmin
        obtain ⟨uu', huu', huu'min⟩ := humin
        have hst : stage s' = 0 := by rw [stage, hd0, orank_bot]
        have hpv : predSet (s'.regs Reg.v) = ∅ := by rw [hvv']; exact predSet_of_isMin hvv'min
        have hpu : predSet (s'.regs Reg.u) = ∅ := by rw [huu']; exact predSet_of_isMin huu'min
        refine ⟨⟨⟨vv', hvv'⟩, ?_, ?_, ?_, ?_, ?_⟩, uu', huu'⟩
        · rw [orank_covBy hcc, hcv, hst]
          exact ncard_inter_predSet_isMax_of_mem (P := {x | S x}) (pW_coe.mp htop) (pW_coe.mp hsrc)
        · rw [hc20, orank_bot, hpv, Set.inter_empty, Set.ncard_empty]
        · rw [hcnt0, orank_bot]
          exact Nat.zero_le _
        · intro htrue
          rw [hflag] at htrue
          exact absurd htrue (by simp)
        · intro y hy
          rw [hpu, Set.inter_empty] at hy
          exact absurd hy (Set.notMem_empty y)
      · obtain ⟨hnsrc, hcc, htop, hd0, hc20, hcnt0, hvmin, humin⟩ := hsat
        rw [hvv] at hnsrc htop
        obtain ⟨vv', hvv', hvv'min⟩ := hvmin
        obtain ⟨uu', huu', huu'min⟩ := humin
        have hst : stage s' = 0 := by rw [stage, hd0, orank_bot]
        have hpv : predSet (s'.regs Reg.v) = ∅ := by rw [hvv']; exact predSet_of_isMin hvv'min
        have hpu : predSet (s'.regs Reg.u) = ∅ := by rw [huu']; exact predSet_of_isMin huu'min
        refine ⟨⟨⟨vv', hvv'⟩, ?_, ?_, ?_, ?_, ?_⟩, uu', huu'⟩
        · rw [← hcc, hcv, hst]
          exact ncard_inter_predSet_isMax_of_notMem (P := {x | S x}) (pW_coe.mp htop)
            (fun h => hnsrc (pW_coe.mpr h))
        · rw [hc20, orank_bot, hpv, Set.inter_empty, Set.ncard_empty]
        · rw [hcnt0, orank_bot]
          exact Nat.zero_le _
        · intro htrue
          rw [hflag] at htrue
          exact absurd htrue (by simp)
        · intro y hy
          rw [hpu, Set.inter_empty] at hy
          exact absurd hy (Set.notMem_empty y)
    · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil

/-- The inner loop: skipping a node, certifying a node, or ending the scan. -/
theorem inv_step_inner {s s' : Cfg V} (hp : s.phase = Phase.inner)
    (hinv : Inv E S T s) (hstep : CfgStep E S T s s') : Inv E S T s' := by
  obtain ⟨l, hl, hsat⟩ := hstep
  have hinv' : PhaseInv E S T Phase.inner s := hp ▸ hinv
  obtain ⟨hinner, uu, huu⟩ := hinv'
  rw [huu] at hinner
  change PhaseInv E S T s'.phase s'
  rw [hp] at hl
  cases hq : s'.phase <;> rw [hq] at hl <;> simp only [table] at hl
  · exact absurd hl List.not_mem_nil
  -- skipping the node
  · split_ifs at hl with hflag
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
      obtain ⟨hucov, hd, hc, hc2, hv, hcnt⟩ := hsat
      rw [huu] at hucov
      obtain ⟨uu', huu', -⟩ := exists_coe_of_covBy hucov
      refine ⟨?_, uu', huu'⟩
      rw [predSet_of_covBy hucov]
      exact innerInv_skip hinner (notMem_predSet_self uu)
        (by rw [stage, stage, hd]) hc.symm hc2.symm hv.symm hcnt.symm hflag.symm
    · exact absurd hl List.not_mem_nil
  -- certifying the node: the walk begins
  · split_ifs at hl with hflag
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
      obtain ⟨hntgt, hwu, hjd, hd, hc, hc2, hv, hcnt, hu⟩ := hsat
      have hstage : stage s' = stage s := by rw [stage, stage, hd]
      refine ⟨?_, ?_, uu, uu, ?_, ?_, ?_, ?_⟩
      · rw [← hu, huu]
        exact innerInv_congr hinner hstage hc.symm hc2.symm hv.symm hcnt.symm hflag.symm
      · rw [← hjd, hstage, stage]
      · rw [← hwu, huu]
      · rw [← hu, huu]
      · rw [show stage s' - orank (s'.regs Reg.j) = 0 by rw [← hjd, hstage, stage]; omega]
        rfl
      · rw [huu] at hntgt
        exact fun h => hntgt (pW_coe.mpr h)
    · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  -- the scan is over
  · split_ifs at hl with hflag
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
      obtain ⟨htop, hd, hc, hc2, hv, hcnt⟩ := hsat
      rw [huu] at htop
      have := innerInv_skip hinner (notMem_predSet_self uu)
        (by rw [stage, stage, hd]) hc.symm hc2.symm hv.symm hcnt.symm hflag.symm
      rwa [insert_predSet_of_isMax (pW_coe.mp htop)] at this
    · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil

/-- The certifying walk: one more edge backwards, or a source is reached. -/
theorem inv_step_walk {s s' : Cfg V} (hp : s.phase = Phase.walk)
    (hinv : Inv E S T s) (hstep : CfgStep E S T s s') : Inv E S T s' := by
  obtain ⟨l, hl, hsat⟩ := hstep
  have hinv' : PhaseInv E S T Phase.walk s := hp ▸ hinv
  obtain ⟨hinner, hjle, ww, uu, hww, huu, hwalk, hnT⟩ := hinv'
  change PhaseInv E S T s'.phase s'
  rw [hp] at hl
  cases hq : s'.phase <;> rw [hq] at hl <;> simp only [table] at hl
  · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  -- one more edge backwards
  · split_ifs at hl with hflag
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
      obtain ⟨hjcov, hedge, hd, hc, hc2, hv, hcnt, hu⟩ := hsat
      have hstage : stage s' = stage s := by rw [stage, stage, hd]
      obtain ⟨ww', ww₂, hww', hww₂, hE⟩ := hedge
      rw [hww] at hww₂
      have hww₂' : ww₂ = ww := (WithBot.coe_inj.mp hww₂.symm)
      subst hww₂'
      have hj : orank (s.regs Reg.j) = orank (s'.regs Reg.j) + 1 := orank_covBy hjcov
      refine ⟨?_, ?_, ww', uu, hww', ?_, ?_, hnT⟩
      · rw [← hu, huu, ← huu]
        exact innerInv_congr (by rw [hu] at hinner ⊢; exact hinner) hstage hc.symm hc2.symm
          hv.symm hcnt.symm hflag.symm
      · rw [hstage]; omega
      · rw [← hu]; exact huu
      · have harith : stage s' - orank (s'.regs Reg.j) = (stage s - orank (s.regs Reg.j)) + 1 := by
          rw [hstage]; omega
        rw [harith]
        exact RInLe.cons hE hwalk
    · exact absurd hl List.not_mem_nil
  -- a source is reached: the node is certified
  · split_ifs at hl with hflag
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
      obtain ⟨hsrcw, hd, hc, hc2, hv, hcnt, hu⟩ := hsat
      have hstage : stage s' = stage s := by rw [stage, stage, hd]
      rw [hww] at hsrcw
      have hmem : uu ∈ Rset E S (stage s) := by
        have h0 : uu ∈ Rset E S (0 + (stage s - orank (s.regs Reg.j))) :=
          mem_rset_of_rInLe (pW_coe.mp hsrcw) hwalk
        rw [Nat.zero_add] at h0
        exact Rset.mono (Nat.sub_le _ _) h0
      refine ⟨?_, uu, by rw [← hu]; exact huu, ?_, hnT⟩
      · rw [← hu, huu, ← huu]
        exact innerInv_congr (by rw [hu] at hinner ⊢; exact hinner) hstage hc.symm hc2.symm
          hv.symm hcnt.symm hflag.symm
      · rw [hstage]; exact hmem
    · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil


/-- The end of a stage: either the counts agree, and the reachable set is the
current layer, or the machine moves on to the next layer. -/
theorem inv_step_stageEnd {s s' : Cfg V} (hp : s.phase = Phase.stageEnd)
    (hinv : Inv E S T s) (hstep : CfgStep E S T s s') : Inv E S T s' := by
  obtain ⟨l, hl, hsat⟩ := hstep
  have hinv' : PhaseInv E S T Phase.stageEnd s := hp ▸ hinv
  obtain ⟨hcv, hc2v, hnoT⟩ := hinv'
  change PhaseInv E S T s'.phase s'
  rw [hp] at hl
  cases hq : s'.phase <;> rw [hq] at hl <;> simp only [table] at hl
  · exact absurd hl List.not_mem_nil
  -- to the inner loop of the next stage
  · split_ifs at hl with hflag
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
      obtain ⟨hd, hc, hc2, hcnt, hv, hu⟩ := hsat
      obtain ⟨vv, hvv, hvmin⟩ := hv
      obtain ⟨uu, huu, humin⟩ := hu
      have hstage : stage s' = stage s + 1 := orank_covBy hd
      have hpv : predSet (s'.regs Reg.v) = ∅ := by rw [hvv]; exact predSet_of_isMin hvmin
      have hpu : predSet (s'.regs Reg.u) = ∅ := by rw [huu]; exact predSet_of_isMin humin
      refine ⟨⟨⟨vv, hvv⟩, ?_, ?_, ?_, ?_, ?_⟩, uu, huu⟩
      · rw [hstage, ← hc, hc2v]
      · rw [hc2, hpv, orank_bot, Set.inter_empty, Set.ncard_empty]
      · rw [hcnt, orank_bot]
        exact Nat.zero_le _
      · intro htrue
        rw [hflag] at htrue
        exact absurd htrue (by simp)
      · intro y hy
        rw [hpu, Set.inter_empty] at hy
        exact absurd hy (Set.notMem_empty y)
    · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  -- acceptance
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    subst hl
    simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
    have hcard : (Rset E S (stage s + 1)).ncard ≤ (Rset E S (stage s)).ncard := by
      rw [← hcv, ← hc2v, hsat]
    have hstab : Rset E S (stage s + 1) = Rset E S (stage s) :=
      (Set.eq_of_subset_of_ncard_le Rset.subset_succ hcard (Set.toFinite _)).symm
    exact not_reach_target_of_stable hstab hnoT


omit [Finite V] in
/-- At the end of the inner scan the count check leaves no room: the certified
nodes are exactly the layer, so no target lies in it and the flag says exactly
whether the outer node has entered the next layer. -/
theorem check_exact {s : Cfg V} (hinv : InnerInv E S T s Set.univ)
    (hcnt : s.regs Reg.cnt = s.regs Reg.c) :
    (∀ y ∈ Rset E S (stage s), ¬T y) ∧
      ∀ vv : V, s.regs Reg.v = ↑vv → (s.flag = true ↔ vv ∈ Rset E S (stage s + 1)) := by
  obtain ⟨-, hcv, -, hcntv, hflagv, hdef⟩ := hinv
  rw [Set.inter_univ] at hcntv hdef
  have hcnteq : orank (s.regs Reg.cnt) = (Rset E S (stage s)).ncard := by rw [hcnt, hcv]
  refine ⟨fun y hy hTy => ?_, fun vv hvv => ⟨fun htrue => ?_, fun hmem => ?_⟩⟩
  · have := hdef y hy (Or.inl hTy)
    omega
  · obtain ⟨vv', hvv', hmem⟩ := hflagv htrue
    rw [hvv] at hvv'
    exact (WithBot.coe_inj.mp hvv'.symm) ▸ hmem
  · by_contra hfalse
    have hf : s.flag = false := by
      cases hfl : s.flag with
      | false => rfl
      | true => exact absurd hfl hfalse
    obtain ⟨y, hy, hwit⟩ := mem_rset_succ_iff_wit.mp hmem
    rw [← hvv] at hwit
    have := hdef y hy (Or.inr ⟨hf, hwit⟩)
    omega

/-- A certified node is counted in, and tested against the outer node. -/
theorem inv_step_certDone {s s' : Cfg V} (hp : s.phase = Phase.certDone)
    (hinv : Inv E S T s) (hstep : CfgStep E S T s s') : Inv E S T s' := by
  obtain ⟨l, hl, hsat⟩ := hstep
  have hinv' : PhaseInv E S T Phase.certDone s := hp ▸ hinv
  obtain ⟨hinner, uu, huu, huR, huT⟩ := hinv'
  rw [huu] at hinner
  change PhaseInv E S T s'.phase s'
  rw [hp] at hl
  cases hq : s'.phase <;> rw [hq] at hl <;> simp only [table] at hl
  · exact absurd hl List.not_mem_nil
  -- on to the next node of the inner scan
  · rw [List.mem_append] at hl
    rcases hl with hl | hl
    · split_ifs at hl with hf
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;>
          simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
        · obtain ⟨heq, hcntcov, hucov, hd, hc, hc2, hv⟩ := hsat
          rw [huu] at hucov
          obtain ⟨uu', huu', -⟩ := exists_coe_of_covBy hucov
          refine ⟨?_, uu', huu'⟩
          rw [predSet_of_covBy hucov]
          exact innerInv_certify hinner (notMem_predSet_self uu) huR huT
            (by rw [stage, stage, hd]) hc.symm hc2.symm hv.symm hcntcov
            (Or.inl ⟨Or.inl (by rw [← huu]; exact heq), hf⟩)
        · obtain ⟨hedge, hcntcov, hucov, hd, hc, hc2, hv⟩ := hsat
          rw [huu] at hucov hedge
          obtain ⟨uu', huu', -⟩ := exists_coe_of_covBy hucov
          refine ⟨?_, uu', huu'⟩
          rw [predSet_of_covBy hucov]
          exact innerInv_certify hinner (notMem_predSet_self uu) huR huT
            (by rw [stage, stage, hd]) hc.symm hc2.symm hv.symm hcntcov
            (Or.inl ⟨Or.inr hedge, hf⟩)
      · exact absurd hl List.not_mem_nil
    · split_ifs at hl with hf
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        subst hl
        simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
        obtain ⟨hne, hnedge, hcntcov, hucov, hd, hc, hc2, hv⟩ := hsat
        rw [huu] at hucov hne hnedge
        obtain ⟨uu', huu', -⟩ := exists_coe_of_covBy hucov
        refine ⟨?_, uu', huu'⟩
        rw [predSet_of_covBy hucov]
        exact innerInv_certify hinner (notMem_predSet_self uu) huR huT
          (by rw [stage, stage, hd]) hc.symm hc2.symm hv.symm hcntcov
          (Or.inr ⟨fun hw => hw.elim hne hnedge, hf.symm⟩)
      · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  -- the certified node was the last one
  · rw [List.mem_append] at hl
    rcases hl with hl | hl
    · split_ifs at hl with hf
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl <;>
          simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
        · obtain ⟨heq, hcntcov, htop, hd, hc, hc2, hv⟩ := hsat
          rw [huu] at htop
          have := innerInv_certify hinner (notMem_predSet_self uu) huR huT
            (by rw [stage, stage, hd]) hc.symm hc2.symm hv.symm hcntcov
            (Or.inl ⟨Or.inl (by rw [← huu]; exact heq), hf⟩)
          rwa [insert_predSet_of_isMax (pW_coe.mp htop)] at this
        · obtain ⟨hedge, hcntcov, htop, hd, hc, hc2, hv⟩ := hsat
          rw [huu] at htop hedge
          have := innerInv_certify hinner (notMem_predSet_self uu) huR huT
            (by rw [stage, stage, hd]) hc.symm hc2.symm hv.symm hcntcov
            (Or.inl ⟨Or.inr hedge, hf⟩)
          rwa [insert_predSet_of_isMax (pW_coe.mp htop)] at this
      · exact absurd hl List.not_mem_nil
    · split_ifs at hl with hf
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        subst hl
        simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
        obtain ⟨hne, hnedge, hcntcov, htop, hd, hc, hc2, hv⟩ := hsat
        rw [huu] at htop hne hnedge
        have := innerInv_certify hinner (notMem_predSet_self uu) huR huT
          (by rw [stage, stage, hd]) hc.symm hc2.symm hv.symm hcntcov
          (Or.inr ⟨fun hw => hw.elim hne hnedge, hf.symm⟩)
        rwa [insert_predSet_of_isMax (pW_coe.mp htop)] at this
      · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil

/-- The count check: the outer count is updated and the scan restarts, or the
stage is over. -/
theorem inv_step_check {s s' : Cfg V} (hp : s.phase = Phase.check)
    (hinv : Inv E S T s) (hstep : CfgStep E S T s s') : Inv E S T s' := by
  obtain ⟨l, hl, hsat⟩ := hstep
  have hinner : InnerInv E S T s Set.univ := by
    have h : PhaseInv E S T Phase.check s := hp ▸ hinv
    exact h
  obtain ⟨vv, hvv⟩ := hinner.1
  have hcv : orank (s.regs Reg.c) = (Rset E S (stage s)).ncard := hinner.2.1
  have hc2v : orank (s.regs Reg.c2) =
      (Rset E S (stage s + 1) ∩ predSet (s.regs Reg.v)).ncard := hinner.2.2.1
  change PhaseInv E S T s'.phase s'
  rw [hp] at hl
  cases hq : s'.phase <;> rw [hq] at hl <;> simp only [table] at hl
  · exact absurd hl List.not_mem_nil
  -- the next node of the outer scan
  · split_ifs at hl with hflag hfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
      obtain ⟨hc2u, hcntc, hvcov, hcnt0, humin, hd, hc⟩ := hsat
      obtain ⟨hnoT, hexact⟩ := check_exact hinner hcntc
      rw [hvv] at hvcov hc2v
      obtain ⟨vv', hvv', -⟩ := exists_coe_of_covBy hvcov
      obtain ⟨uu', huu', huu'min⟩ := humin
      have hstage : stage s' = stage s := by rw [stage, stage, hd]
      have hpu : predSet (s'.regs Reg.u) = ∅ := by rw [huu']; exact predSet_of_isMin huu'min
      refine ⟨⟨⟨vv', hvv'⟩, ?_, ?_, ?_, ?_, ?_⟩, uu', huu'⟩
      · rw [hstage, ← hc, hcv]
      · rw [hstage, orank_covBy hc2u, hc2v,
          ← ncard_inter_predSet_covBy_of_mem hvcov ((hexact vv hvv).mp hfl)]
      · rw [hcnt0, orank_bot]
        exact Nat.zero_le _
      · intro htrue
        rw [hflag] at htrue
        exact absurd htrue (by simp)
      · intro y hy
        rw [hpu, Set.inter_empty] at hy
        exact absurd hy (Set.notMem_empty y)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
      obtain ⟨hc2u, hcntc, hvcov, hcnt0, humin, hd, hc⟩ := hsat
      obtain ⟨hnoT, hexact⟩ := check_exact hinner hcntc
      have hfl' : s.flag = false := by simpa using hfl
      rw [hvv] at hvcov hc2v
      obtain ⟨vv', hvv', -⟩ := exists_coe_of_covBy hvcov
      obtain ⟨uu', huu', huu'min⟩ := humin
      have hstage : stage s' = stage s := by rw [stage, stage, hd]
      have hpu : predSet (s'.regs Reg.u) = ∅ := by rw [huu']; exact predSet_of_isMin huu'min
      have hnotmem : vv ∉ Rset E S (stage s + 1) := fun h => by
        rw [(hexact vv hvv).mpr h] at hfl'
        exact absurd hfl' (by simp)
      refine ⟨⟨⟨vv', hvv'⟩, ?_, ?_, ?_, ?_, ?_⟩, uu', huu'⟩
      · rw [hstage, ← hc, hcv]
      · rw [hstage, ← hc2u, hc2v, ← ncard_inter_predSet_covBy_of_notMem hvcov hnotmem]
      · rw [hcnt0, orank_bot]
        exact Nat.zero_le _
      · intro htrue
        rw [hflag] at htrue
        exact absurd htrue (by simp)
      · intro y hy
        rw [hpu, Set.inter_empty] at hy
        exact absurd hy (Set.notMem_empty y)
    · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil
  -- the outer scan is over: the stage ends
  · split_ifs at hl with hflag hfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
      obtain ⟨hc2u, hcntc, htopv, hd, hc⟩ := hsat
      obtain ⟨hnoT, hexact⟩ := check_exact hinner hcntc
      rw [hvv] at htopv hc2v
      have hstage : stage s' = stage s := by rw [stage, stage, hd]
      refine ⟨by rw [hstage, ← hc, hcv], ?_, by rw [hstage]; exact hnoT⟩
      rw [hstage, orank_covBy hc2u, hc2v]
      exact ncard_inter_predSet_isMax_of_mem (pW_coe.mp htopv) ((hexact vv hvv).mp hfl)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl
      simp only [sat_cons, sat_nil, VAtom.Holds, slotVal, and_true] at hsat
      obtain ⟨hc2u, hcntc, htopv, hd, hc⟩ := hsat
      obtain ⟨hnoT, hexact⟩ := check_exact hinner hcntc
      have hfl' : s.flag = false := by simpa using hfl
      rw [hvv] at htopv hc2v
      have hstage : stage s' = stage s := by rw [stage, stage, hd]
      have hnotmem : vv ∉ Rset E S (stage s + 1) := fun h => by
        rw [(hexact vv hvv).mpr h] at hfl'
        exact absurd hfl' (by simp)
      refine ⟨by rw [hstage, ← hc, hcv], ?_, by rw [hstage]; exact hnoT⟩
      rw [hstage, ← hc2u, hc2v]
      exact ncard_inter_predSet_isMax_of_notMem (pW_coe.mp htopv) hnotmem
    · exact absurd hl List.not_mem_nil
  · exact absurd hl List.not_mem_nil

omit [Finite V] in
/-- Nothing leaves the accepting phase. -/
theorem inv_step_accept {s s' : Cfg V} (hp : s.phase = Phase.accept)
    (_hinv : Inv E S T s) (hstep : CfgStep E S T s s') : Inv E S T s' := by
  obtain ⟨l, hl, -⟩ := hstep
  rw [hp] at hl
  cases hq : s'.phase <;> rw [hq] at hl <;> simp only [table] at hl <;>
    exact absurd hl List.not_mem_nil

/-! ### Soundness -/

/-- **The invariant is preserved by every transition.** -/
theorem inv_step {s s' : Cfg V} (hinv : Inv E S T s) (hstep : CfgStep E S T s s') :
    Inv E S T s' := by
  cases hp : s.phase with
  | initCount => exact inv_step_initCount hp hinv hstep
  | inner => exact inv_step_inner hp hinv hstep
  | walk => exact inv_step_walk hp hinv hstep
  | certDone => exact inv_step_certDone hp hinv hstep
  | check => exact inv_step_check hp hinv hstep
  | stageEnd => exact inv_step_stageEnd hp hinv hstep
  | accept => exact inv_step_accept hp hinv hstep

omit [Finite V] in
/-- The invariant holds at every initial configuration. -/
theorem inv_of_isSrc {s : Cfg V} (h : CfgIsSrc s) : Inv E S T s := by
  obtain ⟨hph, -, hc, vv, hvv, hvmin⟩ := h
  change PhaseInv E S T s.phase s
  rw [hph]
  exact ⟨⟨vv, hvv⟩, by
    rw [hc, orank_bot, hvv, predSet_of_isMin hvmin, Set.inter_empty, Set.ncard_empty]⟩

/-- The invariant survives any number of transitions. -/
theorem inv_reach {s s' : Cfg V} (hinv : Inv E S T s) (h : CfgReach E S T s s') :
    Inv E S T s' := by
  induction h with
  | refl => exact hinv
  | @tail b c _ hbc ih => exact inv_step ih hbc

/-- **Soundness**: if the machine accepts, no target is reachable from a
source. -/
theorem not_reach_of_machineAccepts (h : MachineAccepts E S T) :
    ¬∃ a b : V, S a ∧ T b ∧ Relation.ReflTransGen E a b := by
  obtain ⟨s, s', hsrc, htgt, hreach⟩ := h
  have hinv : Inv E S T s' := inv_reach (inv_of_isSrc hsrc) hreach
  change PhaseInv E S T s'.phase s' at hinv
  rw [htgt] at hinv
  exact hinv

end Sound

end InductiveCounting

end DescriptiveComplexity
