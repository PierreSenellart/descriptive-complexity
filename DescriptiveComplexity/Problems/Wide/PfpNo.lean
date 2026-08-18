/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpYes
import DescriptiveComplexity.Problems.Wide.PfpHalt

/-!
# A partial fixed point that fails makes the machine reject

The converse half of the EXPSPACE reduction, in the case the iteration
**converges**. No invariant over the program's rules appears: the machine is
deterministic, so the configurations reachable from its initial one are
linearly ordered, and it is enough to exhibit *one* run that ends badly
(`DescriptiveComplexity.TMData.not_acceptsSpace_of_reaches_dead`). That run is
the one `DescriptiveComplexity.Pfp.PfpData.reaches_outVerdict` already
produces: it lands in the accepting phase whatever the verdict, and the
accepting *predicate* there is equivalent to the value of the fixed point. So
a fixed point that fails leaves the machine in a phase it cannot leave
(`DescriptiveComplexity.Pfp.PfpData.stuck_acc`) and does not accept in.

What is left of soundness is the diverging case, where the machine has no
halting configuration to reach at all and
`DescriptiveComplexity.TMData.not_acceptsSpace_of_chain` takes over.
-/

namespace DescriptiveComplexity

namespace Pfp

namespace PfpData

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}} {dt : PfpData L} {A : Type} {zero one : A}
variable [LinearOrder A] [Fintype dt.SlotIx]
variable [Finite A] [Finite dt.KIx]
variable [Nonempty A] [L.IsRelational] [L.Structure A]
variable {hzo : zero ≠ one}
variable [LinearOrder (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))]
variable [LinearOrder dt.PF]
variable {hpl : Fintype.card (dt.CtlIx ⊕ dt.SlotIx) ≤ dt.dd}
variable [Language.wide.Structure (Univ A
  (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx dt.dd)]
variable [Finite (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))]
variable [Finite dt.PF]
variable [LinearOrder (dt.X.Map A)]

omit [Finite dt.KIx]
  [Language.wide.Structure (Univ A
    (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
    dt.dd)]
  [Finite (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))]
  [Finite dt.PF] [LinearOrder (dt.X.Map A)] in
/-- **The machine's accepting predicate is the program's**, read back: the
converse of `DescriptiveComplexity.Pfp.Prog.accept_table`, the pointer being
recovered from the state's payload by the same equation. -/
theorem accept_of_isAcc
    {p : dt.PF} {f : dt.CtlIx → A}
    (h : (dt.progOf zero one hzo hpl).table.IsAcc
      ((dt.progOf zero one hzo hpl).stElt p f)) :
    (dt.progOf zero one hzo hpl).accept p f := by
  have h2 : (dt.progOf zero one hzo hpl).table.accept p
      (stPl (W := dt.SlotIx) zero f) := by
    have h3 : (dt.progOf zero one hzo hpl).table.accept p
        (unpad (dt.progOf zero one hzo hpl).table.payload_le
          (pad zero (stPl (W := dt.SlotIx) zero f))) := h.2
    rwa [unpad_pad] at h3
  have he : (fun q => unslot (stPl (W := dt.SlotIx) zero f) (Sum.inl q)) = f :=
    funext fun q => by
      rw [stPl, unslot_slotPl]
      exact stVec_inl f q
  change (dt.progOf zero one hzo hpl).accept p
    (fun q => unslot (stPl (W := dt.SlotIx) zero f) (Sum.inl q)) at h2
  rwa [he] at h2

/-- **A converging fixed point that fails makes the emitted instance a
no-instance.** The run of `reaches_outVerdict` ends in the accepting phase,
which no rule leaves, with the accepting predicate equivalent to the value of
the fixed point – so when that value is `False` the run has reached a dead end
that does not accept, and a deterministic machine has no other run. -/
theorem not_dwideAcceptSpace_of_converges
    (hR : (dt.progOf zero one hzo hpl).table.Reads)
    (hdd : dt.dd0 < dt.dd) (i₀ : dt.KIx)
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (hcv : dt.d.PFPConverges (dt.X.Map A))
    (hno : ¬dt.d.PFPHolds (dt.X.Map A)) :
    ¬DWideAcceptSpace (Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd) := by
  classical
  rintro ⟨-, -, hacc⟩
  obtain ⟨cfg, f, hrun, hstate, hiff⟩ :=
    dt.reaches_outVerdict hR hdd i₀ hordP hcv
  have hlin := (dt.progOf zero one hzo hpl).table.isLinOrd_wmLe hR
  refine TMData.not_acceptsSpace_of_reaches_dead
    ((dt.progOf zero one hzo hpl).table.wellFormed hR)
    ((dt.progOf zero one hzo hpl).table.deterministic hR
      (dt.prog_sep zero one hzo (fun w => dt.varArgsOf zero one w) hpl))
    (Prog.isInit_prog hR hlin (fun _ => trivial) (fun x => prog_mark_mir hpl x)
      (prog_blank_mir hpl)) hrun
    (stuck_of_srcPh_ne hR (srcPh_ne_acceptP (hpl := hpl)) hstate) ?_
    (fun e => stuck_acc hR e) hacc
  -- the state it stops in does not accept, the fixed point having failed
  intro hc
  rw [hstate] at hc
  have hc' : WMAcc ((dt.progOf zero one hzo hpl).stElt OuterPh.acceptP f) := hc
  rw [hR.acc] at hc'
  exact hno (hiff.mp (accept_of_isAcc hc'))

/-- **A diverging fixed point makes the emitted instance a no-instance.** The
machine has no clock: when no stage is stable it keeps sweeping, so its run
passes an unbounded chain of stage entries
(`DescriptiveComplexity.Pfp.PfpData.transGen_stageB`, each link at least one
step) and reaches no halting configuration at all – whence
`DescriptiveComplexity.TMData.not_acceptsSpace_of_chain`. -/
theorem not_dwideAcceptSpace_of_diverges
    (hR : (dt.progOf zero one hzo hpl).table.Reads)
    (hdd : dt.dd0 < dt.dd) (i₀ : dt.KIx)
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q)
    (hdv : ¬dt.d.PFPConverges (dt.X.Map A)) :
    ¬DWideAcceptSpace (Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd) := by
  classical
  rintro ⟨-, -, hacc⟩
  have hlin : IsLinOrd (WMLe (A := Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd)) := (dt.progOf zero one hzo hpl).table.isLinOrd_wmLe hR
  have hord := hR.le
  -- the two extremes of the universe
  obtain ⟨gtop, -, htop⟩ := exists_greatest (Le := WMLe (A := Univ A
    (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
    dt.dd)) hlin (P := fun _ => True) ⟨(PfpTag.arg i₀, fun _ => zero), trivial⟩
  obtain ⟨gbot, -, hbot⟩ := exists_least (Le := WMLe (A := Univ A
    (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
    dt.dd)) hlin (P := fun _ => True) ⟨(PfpTag.arg i₀, fun _ => zero), trivial⟩
  simp only [forall_const] at htop hbot
  -- the logical interval
  have hnotbot : ¬logicalTop gbot := by
    rintro ⟨i, hi⟩
    have h := tagBlk_eq_none_of_least (ko := dt.ko) (ki := dt.ki)
      (fun y => (hord gbot y).mp (hbot y))
    rw [hi] at h
    exact absurd h (by simp [tagBlk])
  have hlt : WMSetLt WMLe (logicalTop (R := dt.RIx zero one hzo
      (fun w => dt.varArgsOf zero one w)) (P := dt.PF) (K := dt.KIx)
      (V := Fin dt.dd → A)) (wmSeg gbot) :=
    wmSetLt_wmSeg_of_not_bot hbot hnotbot gbot
  have hneT : ∃ x, logicalTop (R := dt.RIx zero one hzo
      (fun w => dt.varArgsOf zero one w)) (P := dt.PF) (K := dt.KIx)
      (V := Fin dt.dd → A) x := ⟨(PfpTag.arg i₀, fun _ => zero), i₀, rfl⟩
  obtain ⟨v₁, hiE⟩ := exists_wmIncr hlin (s := fun _ : Univ A
    (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
    dt.dd => False) ⟨gbot, not_false⟩
  -- the layout's own placement lemmas, at the instance's order
  have hordL : ∀ x y : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd, WMLe x y ↔ lexRel (· ≤ · : PfpTag (dt.RIx zero one hzo
        (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx →
        PfpTag (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF
          dt.KIx → Prop) (tupLeLex (A := A) (d := dt.dd)) x y :=
    fun x y => (hord x y).trans (Wide.tagTupleLe_iff_lexRel x y)
  -- the VAL enumeration
  obtain ⟨nV, mV, hmV0, hIncr, hTestT, hTestF, hKin⟩ :=
    exists_valEnum (dt := dt) (A := A)
      (R := dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
      (P := dt.PF) hlin hord
  -- every address the dictionary is read at lies in the logical interval
  have hbelow : ∀ (j : Fin dt.nv) (a : Fin (nV + 1)) (iv : dt.d.B.ι)
      (ts : Fin (dt.d.B.arity iv) → Fin (dt.nOf (dt.varAt j)))
      (st : TapeStD dt A
        (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF)
      (w : Univ A (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
        dt.PF dt.KIx dt.dd → Prop),
      WMSetLt WMLe (dt.stageTgtD zero (dt.varAt j) iv ts
        (dt.roundSt st (mV a)) w (dt.d.B.arity iv)) logicalTop :=
    fun _ _ _ _ _ _ => (wmSetLt_congr_rel hordL _ _).mpr
      (dt.wmSetLt_stageTgtD_logicalTop hzo Wide.isLinOrd_tupLeLex hdd i₀ _)
  have hS : ∀ (iv : dt.d.B.ι) (x : Fin (dt.d.B.arity iv) → dt.X.Map A),
      WMSetLt WMLe (tupAddr dt.ly zero one
        (R := dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
        (P := dt.PF) (ki := dt.ki) (dt.arOf_le_ko (some iv)) x) logicalTop :=
    fun iv x => (wmSetLt_congr_rel hordL _ _).mpr
      (wmSetLt_tupAddr_logicalTop' hzo Wide.isLinOrd_tupLeLex i₀
        (dt.arOf_le_ko (some iv)) x)
  -- the initial tape is stage zero
  have hold₀ : ∀ (iv : dt.d.B.ι) (s : Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd → Prop), WMSetLt WMLe s logicalTop →
      ((dt.startupSt (A := A)
          (R' := dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w))
          (P' := dt.PF)).old iv s ↔
        trackOf dt.ly zero one (dt.arOf_le_ko (some iv))
          (dt.d.partStage (dt.X.Map A) 0) s) :=
    fun iv s _ => old_trackOf_zero_of_blank (fun _ _ hc => hc) iv s
  -- no stage is stable, so every convergence test fails
  have hmove : ∀ n, dt.d.partStage (dt.X.Map A) n ≠
      dt.d.partStage (dt.X.Map A) (n + 1) :=
    fun n hc => hdv ⟨n, ((dt.d.partStage_succ (A := dt.X.Map A) n).symm.trans
      hc.symm : Function.IsFixedPt dt.d.next _)⟩
  have hnotconv := fun n => dt.stageEnd_not_conv_of_ne
    (hpl := hpl) (hlin := hlin) (hord := hord) (hbot := hbot)
    (hbotV := fun a : Fin (nV + 1) => Fin.zero_le a) (mV := mV)
    (hmV0 := hmV0) (hIncr := hIncr) (hTestT := hTestT)
    (st₀ := dt.startupSt) (f₀ := fun _ => zero) (ltpAddr := logicalTop)
    (hordP := hordP) (hKin := hKin) (hlt := hlt) (hold₀ := hold₀)
    (hbelow := hbelow) (hS := hS) (hN := hmove n)
  -- the chain of stage entries, and the run into the first of them
  have hchain := fun n => dt.transGen_stageB (hpl := hpl) (hR := hR)
    (hlin := hlin) (hord := hord) (htop := htop) (hbot := hbot)
    (hbotV := fun a : Fin (nV + 1) => Fin.zero_le a)
    (htopV := fun a : Fin (nV + 1) => Fin.le_last a) (mV := mV)
    (hmV0 := hmV0) (hIncr := hIncr) (hTestT := hTestT) (hTestF := hTestF)
    (semAt := fun w j st hg => dt.gatedSem
      (PR := dt.progOf zero one hzo hpl) (wmSegFile hlin) hzo hlin mV (v := w) j st hg)
    (st₀ := dt.startupSt) (f₀ := fun _ => zero) (ltpAddr := logicalTop)
    (hlt := hlt) (hneT := hneT) (hwk₀ := startupSt_wk)
    (hmir₀ := startupSt_mir) (hbot₀ := startupSt_bot)
    (hltp₀ := startupSt_ltp) (n := n) (hnc := hnotconv n)
  have hentry := dt.reaches_evalEntry (hpl := hpl) (hR := hR) (hlin := hlin)
    (hord := hord) (htop := htop) (hbot := hbot)
  refine TMData.not_acceptsSpace_of_chain
    ((dt.progOf zero one hzo hpl).table.wellFormed hR)
    ((dt.progOf zero one hzo hpl).table.deterministic hR
      (dt.prog_sep zero one hzo (fun w => dt.varArgsOf zero one w) hpl))
    (Prog.isInit_prog hR hlin (fun _ => trivial) (fun x => prog_mark_mir hpl x)
      (prog_blank_mir hpl)) ?_ hchain (fun e => stuck_acc hR e) hacc
  rw [dt.initBack_eq_back zero one hzo (fun w => dt.varArgsOf zero one w) hpl
    hlin]
  exact hentry

/-! ### The reduction is correct -/

/-- **The emitted instance is a yes-instance exactly when the partial fixed
point holds.** The three cases of the trichotomy are the three theorems above:
a fixed point that holds is run into the accepting phase; one that converges
and fails leaves the machine at a dead end; and one that diverges keeps it
sweeping for ever. Nothing here is an induction over the program's rules – the
machine's determinism does that work, and the only side condition is that its
accepting phase is a dead end. -/
theorem dwideAcceptSpace_iff_pfpHolds
    (hR : (dt.progOf zero one hzo hpl).table.Reads)
    (hdd : dt.dd0 < dt.dd) (i₀ : dt.KIx)
    (hordP : ∀ p q : dt.X.Map A,
      p ≤ q ↔ (encOrder dt.ly zero one hzo).le p q) :
    DWideAcceptSpace (Univ A
      (dt.RIx zero one hzo (fun w => dt.varArgsOf zero one w)) dt.PF dt.KIx
      dt.dd) ↔ dt.d.PFPHolds (dt.X.Map A) := by
  classical
  refine ⟨fun h => by_contra fun hno => ?_,
    dt.dwideAcceptSpace_of_pfpHolds hR hdd i₀ hordP⟩
  by_cases hcv : dt.d.PFPConverges (dt.X.Map A)
  · exact dt.not_dwideAcceptSpace_of_converges hR hdd i₀ hordP hcv hno h
  · exact dt.not_dwideAcceptSpace_of_diverges hR hdd i₀ hordP hcv h

end PfpData

end Pfp

end DescriptiveComplexity
