/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.JobSequencing.Kernel

/-!
# Job sequencing is in NP

The bridge between the kernel of `DescriptiveComplexity.Problems.JobSequencing.Kernel`
and what it means: `DescriptiveComplexity.realize_jobSequencingKernel` reads each
clause back as a statement about the guessed relations, so that the two
directions of the `Σ₁` definition can be argued with
`DescriptiveComplexity.chain_sound` and `DescriptiveComplexity.exists_chain` for the
walks and `DescriptiveComplexity.binNum_lt_iff` for the two comparisons.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SOBlock

section SigmaOne

section Realize

variable {A : Type} [Language.jobSeq.Structure A]
variable (ρ : jobSeqGuessBlock.Assignment A)

theorem realize_jobSequencingKernel :
    (@Sentence.Realize jqSOLang A
        (@sumStructure _ _ A _ (jobSeqGuessBlock.structure ρ)) jobSequencingKernel) ↔
      (IsLinOrd (JSLe (A := A)) ∧ IsLinOrd (JSched ρ)) ∧
        (∀ j : A, JLate ρ j → JSJob j) ∧
        (∀ s : Bool,
          (∀ i x p : A, MinPos (JOrd ρ s) JSJob i → JSPosn p →
            (JPS ρ s i (x, p) ↔ ChainAdd (JSel ρ s) (JWt s) i (x, p))) ∧
          (∀ i j x p : A, SuccPos (JOrd ρ s) JSJob i j → JSPosn p →
            (JPS ρ s j (x, p) ↔ (JPS ρ s i (x, p) ↔
              (ChainAdd (JSel ρ s) (JWt s) j (x, p) ↔ JCy ρ s j (x, p))))) ∧
          (∀ i j x p y q : A, SuccPos (JOrd ρ s) JSJob i j →
            ((x = y ∧ SuccPos JSLe JSPosn p q) ∨
              (SuccPos JSLe (fun _ => True) x y ∧ MaxPos JSLe JSPosn p ∧
                MinPos JSLe JSPosn q)) →
            (JCy ρ s j (y, q) ↔ maj (JPS ρ s i (x, p))
              (ChainAdd (JSel ρ s) (JWt s) j (x, p)) (JCy ρ s j (x, p)))) ∧
          (∀ i j x p : A, SuccPos (JOrd ρ s) JSJob i j →
            ((∀ y : A, JSLe x y) ∧ MinPos JSLe JSPosn p) → ¬JCy ρ s j (x, p)) ∧
          (∀ i j x p : A, SuccPos (JOrd ρ s) JSJob i j →
            ((∀ y : A, JSLe y x) ∧ MaxPos JSLe JSPosn p) →
            ¬maj (JPS ρ s i (x, p)) (ChainAdd (JSel ρ s) (JWt s) j (x, p))
              (JCy ρ s j (x, p)))) ∧
        (∀ j : A, JSJob j → (JLate ρ j ↔ ∃ x p : A, JSPosn p ∧ ¬JDlineW j (x, p) ∧
          JPS ρ true j (x, p) ∧ ∀ y q : A, JSPosn q →
            (((JSLe x y ∧ ¬x = y) ∨ (x = y ∧ JSLe p q)) ∧ (¬y = x ∨ ¬q = p)) →
            (JDlineW j (y, q) ↔ JPS ρ true j (y, q)))) ∧
        (∀ j : A, MaxPos JSLe JSJob j → ¬∃ x p : A, JSPosn p ∧ ¬JBndW (x, p) ∧
          JPS ρ false j (x, p) ∧ ∀ y q : A, JSPosn q →
            (((JSLe x y ∧ ¬x = y) ∨ (x = y ∧ JSLe p q)) ∧ (¬y = x ∨ ¬q = p)) →
            (JBndW (y, q) ↔ JPS ρ false j (y, q))) := by
  letI := jobSeqGuessBlock.structure ρ
  have hsubS : ∀ w : Fin 2 → A,
      RelMap (L := jqSOLang) (M := A) jqSchedSym w ↔ ρ .sched w := fun _ => Iff.rfl
  have hsubL : ∀ w : Fin 1 → A,
      RelMap (L := jqSOLang) (M := A) jqLateSym w ↔ ρ .late w := fun _ => Iff.rfl
  have hsubP : ∀ (s : Bool) (w : Fin 3 → A),
      RelMap (L := jqSOLang) (M := A) (jqPSSym s) w ↔ ρ (.ps s) w := fun _ _ => Iff.rfl
  have hsubC : ∀ (s : Bool) (w : Fin 3 → A),
      RelMap (L := jqSOLang) (M := A) (jqCySym s) w ↔ ρ (.cy s) w := fun _ _ => Iff.rfl
  rw [jobSequencingKernel]
  simp only [jqReflClause, jqTransClause, jqAntisymmClause, jqTotalClause,
    jqSchedReflClause, jqSchedTransClause, jqSchedAntisymmClause, jqSchedTotalClause,
    jqLateJobClause, jqWalkClauses, jqBaseClause, jqSumClause, jqCarryClause,
    jqBottomClause, jqTopClause, jqLateDefClause, jqFinalClause, jqJobF, jqPosnF,
    jqTimeF, jqDlineF, jqPenF, jqBndF, jqLeF, jqEqF, jqSchedF, jqLateF, jqPSF, jqCyF,
    jqOrdF, jqSelF, jqWtF, jqBotF, jqTopF, jqAddF, jqDlineWF, jqBndWF, jqXor3F,
    jqMaj3F, jqMinItemF, jqMaxItemF, jqSuccItemF, jqMinPosnF, jqMaxPosnF, jqSuccPosnF,
    jqSuccAllF, jqMinWideF, jqMaxWideF, jqSuccWideF, jqWideLeF, jqWideNeF,
    Sentence.Realize, Formula.realize_inf, Formula.realize_sup, Formula.realize_imp,
    Formula.realize_iff, Formula.realize_not, Formula.realize_iAlls,
    Formula.realize_iExs, Formula.realize_rel₁, Formula.realize_rel₂, realize_rel₃,
    Formula.realize_equal, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsubS, hsubL, hsubP, hsubC]
  constructor
  · rintro ⟨⟨⟨hrefl, htrans, hanti, htot⟩, hsrefl, hstrans, hsanti, hstot⟩,
      hlate, ⟨hb1, hs1, hc1, hbo1, ht1⟩, ⟨hb0, hs0, hc0, hbo0, ht0⟩, hldef, hfin⟩
    have hminU : ∀ (R : A → A → Prop) (P : A → Prop) (x : A), MinPos R P x →
        P x ∧ ∀ y : Unit → A, P (y ()) → R x (y ()) :=
      fun _ P x h => ⟨h.1, fun y hy => h.2 (y ()) hy⟩
    have hmaxU : ∀ (R : A → A → Prop) (P : A → Prop) (x : A), MaxPos R P x →
        P x ∧ ∀ y : Unit → A, P (y ()) → R (y ()) x :=
      fun _ P x h => ⟨h.1, fun y hy => h.2 (y ()) hy⟩
    have hsuccU : ∀ (R : A → A → Prop) (P : A → Prop) (x y : A), SuccPos R P x y →
        P x ∧ (P y ∧ (R x y ∧ (¬x = y ∧ ∀ r : Unit → A,
          P (r ()) → R x (r ()) → R (r ()) y → r () = x ∨ r () = y))) :=
      fun _ P x y h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        fun r hr h1 h2 => h.2.2.2.2 (r ()) hr h1 h2⟩
    have hsallU : ∀ x y : A, SuccPos JSLe (fun _ => True) x y →
        JSLe x y ∧ (¬x = y ∧ ∀ r : Unit → A,
          JSLe x (r ()) → JSLe (r ()) y → r () = x ∨ r () = y) :=
      fun x y h => ⟨h.2.2.1, h.2.2.2.1, fun r h1 h2 => h.2.2.2.2 (r ()) trivial h1 h2⟩
    refine ⟨⟨⟨fun a => hrefl (fun _ => a),
        fun a b c hab hbc => htrans ![a, b, c] ⟨hab, hbc⟩,
        fun a b hab hba => hanti ![a, b] ⟨hab, hba⟩, fun a b => htot ![a, b]⟩,
      ⟨fun a => hsrefl (fun _ => a), fun a b c hab hbc => hstrans ![a, b, c] ⟨hab, hbc⟩,
        fun a b hab hba => hsanti ![a, b] ⟨hab, hba⟩, fun a b => hstot ![a, b]⟩⟩,
      fun j hj => hlate (fun _ => j) hj, fun s => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · cases s
      · exact ⟨fun i x p hi hp => hb0 ![i, x, p] ⟨hminU _ _ _ hi, hp⟩,
          fun i j x p hij hp => hs0 ![i, j, x, p] ⟨hsuccU _ _ _ _ hij, hp⟩,
          fun i j x p y q hij hpq => hc0 ![i, j, x, p, y, q] ⟨hsuccU _ _ _ _ hij, by
            rcases hpq with ⟨rfl, h⟩ | ⟨h1, h2, h3⟩
            · exact Or.inl ⟨rfl, hsuccU _ _ _ _ h⟩
            · exact Or.inr ⟨hsallU _ _ h1, hmaxU _ _ _ h2, hminU _ _ _ h3⟩⟩,
          fun i j x p hij hp => hbo0 ![i, j, x, p]
            ⟨hsuccU _ _ _ _ hij, fun y => hp.1 (y ()), hminU _ _ _ hp.2⟩,
          fun i j x p hij hp => ht0 ![i, j, x, p]
            ⟨hsuccU _ _ _ _ hij, fun y => hp.1 (y ()), hmaxU _ _ _ hp.2⟩⟩
      · exact ⟨fun i x p hi hp => hb1 ![i, x, p] ⟨hminU _ _ _ hi, hp⟩,
          fun i j x p hij hp => hs1 ![i, j, x, p] ⟨hsuccU _ _ _ _ hij, hp⟩,
          fun i j x p y q hij hpq => hc1 ![i, j, x, p, y, q] ⟨hsuccU _ _ _ _ hij, by
            rcases hpq with ⟨rfl, h⟩ | ⟨h1, h2, h3⟩
            · exact Or.inl ⟨rfl, hsuccU _ _ _ _ h⟩
            · exact Or.inr ⟨hsallU _ _ h1, hmaxU _ _ _ h2, hminU _ _ _ h3⟩⟩,
          fun i j x p hij hp => hbo1 ![i, j, x, p]
            ⟨hsuccU _ _ _ _ hij, fun y => hp.1 (y ()), hminU _ _ _ hp.2⟩,
          fun i j x p hij hp => ht1 ![i, j, x, p]
            ⟨hsuccU _ _ _ _ hij, fun y => hp.1 (y ()), hmaxU _ _ _ hp.2⟩⟩
    · refine (hldef (fun _ => j) hj).trans ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨w, hw⟩ := h
        exact ⟨w 0, w 1, hw.1, hw.2.1, hw.2.2.1, fun y q hq hab =>
          hw.2.2.2 ![y, q] ⟨hq, hab⟩⟩
      · obtain ⟨x, p, hp, h1, h2, h3⟩ := h
        exact ⟨![x, p], hp, h1, h2, fun w hw => h3 (w 0) (w 1) hw.1 hw.2⟩
    · refine (hfin (fun _ => j) (hmaxU _ _ _ hj)).imp fun h => ?_
      obtain ⟨x, p, hp, h1, h2, h3⟩ := h
      exact ⟨![x, p], hp, h1, h2, fun w hw => h3 (w 0) (w 1) hw.1 hw.2⟩
  · rintro ⟨⟨⟨hrefl, htrans, hanti, htot⟩, hsrefl, hstrans, hsanti, hstot⟩,
      hlate, hwalk, hldef, hfin⟩
    have hminM : ∀ (R : A → A → Prop) (P : A → Prop) (x : A),
        (P x ∧ ∀ y : Unit → A, P (y ()) → R x (y ())) → MinPos R P x :=
      fun _ P x h => ⟨h.1, fun y hy => h.2 (fun _ => y) hy⟩
    have hmaxM : ∀ (R : A → A → Prop) (P : A → Prop) (x : A),
        (P x ∧ ∀ y : Unit → A, P (y ()) → R (y ()) x) → MaxPos R P x :=
      fun _ P x h => ⟨h.1, fun y hy => h.2 (fun _ => y) hy⟩
    have hsuccM : ∀ (R : A → A → Prop) (P : A → Prop) (x y : A),
        (P x ∧ (P y ∧ (R x y ∧ (¬x = y ∧ ∀ r : Unit → A,
          P (r ()) → R x (r ()) → R (r ()) y → r () = x ∨ r () = y)))) →
        SuccPos R P x y :=
      fun _ P x y h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        fun r hr h1 h2 => h.2.2.2.2 (fun _ => r) hr h1 h2⟩
    have hsallM : ∀ x y : A,
        (JSLe x y ∧ (¬x = y ∧ ∀ r : Unit → A,
          JSLe x (r ()) → JSLe (r ()) y → r () = x ∨ r () = y)) →
        SuccPos JSLe (fun _ => True) x y :=
      fun x y h => ⟨trivial, trivial, h.1, h.2.1,
        fun r _ h1 h2 => h.2.2 (fun _ => r) h1 h2⟩
    refine ⟨⟨⟨fun w => hrefl (w 0), fun w h => htrans (w 0) (w 1) (w 2) h.1 h.2,
        fun w h => hanti (w 0) (w 1) h.1 h.2, fun w => htot (w 0) (w 1)⟩,
      fun w => hsrefl (w 0), fun w h => hstrans (w 0) (w 1) (w 2) h.1 h.2,
      fun w h => hsanti (w 0) (w 1) h.1 h.2, fun w => hstot (w 0) (w 1)⟩,
      fun w h => hlate (w 0) h, ?_, ?_, ?_, ?_⟩
    · exact ⟨fun w h => (hwalk true).1 (w 0) (w 1) (w 2) (hminM _ _ _ h.1) h.2,
        fun w h => (hwalk true).2.1 (w 0) (w 1) (w 2) (w 3) (hsuccM _ _ _ _ h.1) h.2,
        fun w h => (hwalk true).2.2.1 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)
          (hsuccM _ _ _ _ h.1) (by
            rcases h.2 with ⟨he, h'⟩ | ⟨h1, h2, h3⟩
            · exact Or.inl ⟨he, hsuccM _ _ _ _ h'⟩
            · exact Or.inr ⟨hsallM _ _ h1, hmaxM _ _ _ h2, hminM _ _ _ h3⟩),
        fun w h => (hwalk true).2.2.2.1 (w 0) (w 1) (w 2) (w 3) (hsuccM _ _ _ _ h.1)
          ⟨fun y => h.2.1 (fun _ => y), hminM _ _ _ h.2.2⟩,
        fun w h => (hwalk true).2.2.2.2 (w 0) (w 1) (w 2) (w 3) (hsuccM _ _ _ _ h.1)
          ⟨fun y => h.2.1 (fun _ => y), hmaxM _ _ _ h.2.2⟩⟩
    · exact ⟨fun w h => (hwalk false).1 (w 0) (w 1) (w 2) (hminM _ _ _ h.1) h.2,
        fun w h => (hwalk false).2.1 (w 0) (w 1) (w 2) (w 3) (hsuccM _ _ _ _ h.1) h.2,
        fun w h => (hwalk false).2.2.1 (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)
          (hsuccM _ _ _ _ h.1) (by
            rcases h.2 with ⟨he, h'⟩ | ⟨h1, h2, h3⟩
            · exact Or.inl ⟨he, hsuccM _ _ _ _ h'⟩
            · exact Or.inr ⟨hsallM _ _ h1, hmaxM _ _ _ h2, hminM _ _ _ h3⟩),
        fun w h => (hwalk false).2.2.2.1 (w 0) (w 1) (w 2) (w 3) (hsuccM _ _ _ _ h.1)
          ⟨fun y => h.2.1 (fun _ => y), hminM _ _ _ h.2.2⟩,
        fun w h => (hwalk false).2.2.2.2 (w 0) (w 1) (w 2) (w 3) (hsuccM _ _ _ _ h.1)
          ⟨fun y => h.2.1 (fun _ => y), hmaxM _ _ _ h.2.2⟩⟩
    · refine fun w hj => (hldef (w 0) hj).trans ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨x, p, hp, h1, h2, h3⟩ := h
        exact ⟨![x, p], hp, h1, h2, fun v hv => h3 (v 0) (v 1) hv.1 hv.2⟩
      · obtain ⟨v, hv⟩ := h
        exact ⟨v 0, v 1, hv.1, hv.2.1, hv.2.2.1, fun y q hq hab =>
          hv.2.2.2 ![y, q] ⟨hq, hab⟩⟩
    · refine fun w hj => (hfin (w 0) (hmaxM _ _ _ hj)).imp fun h => ?_
      obtain ⟨v, hv⟩ := h
      exact ⟨v 0, v 1, hv.1, hv.2.1, hv.2.2.1, fun y q hq hab =>
        hv.2.2.2 ![y, q] ⟨hq, hab⟩⟩

end Realize

/-! ### Reading the comparisons back -/

section Compare

variable {A : Type} [Finite A] [Language.jobSeq.Structure A]

/-- **The comparison clauses say what they should**: the shape the kernel
writes – two wide positions, the second strictly above the first written out
coordinate by coordinate – is `DescriptiveComplexity.binNum_lt_iff` on the wide
positions. Both comparisons of the kernel go through this, the deadline
against a completion time and the bound against the penalty total. -/
theorem binNum_wide_lt_iff (hlin : IsLinOrd (JSLe (A := A))) (b b' : A × A → Prop) :
    binNum (wideLe JSLe) (WidePosn JSPosn) b <
        binNum (wideLe JSLe) (WidePosn JSPosn) b' ↔
      ∃ x p : A, JSPosn p ∧ ¬b (x, p) ∧ b' (x, p) ∧ ∀ y q : A, JSPosn q →
        (((JSLe x y ∧ ¬x = y) ∨ (x = y ∧ JSLe p q)) ∧ (¬y = x ∨ ¬q = p)) →
        (b (y, q) ↔ b' (y, q)) := by
  rw [binNum_lt_iff (isLinOrd_wideLe hlin) _ (WidePosn JSPosn) rfl b b']
  constructor
  · rintro ⟨u, hu, hb, hb', habove⟩
    refine ⟨u.1, u.2, hu, hb, hb', fun y q hq hyq => ?_⟩
    refine habove (y, q) hq hyq.1 fun hne => ?_
    rcases hyq.2 with h | h
    · exact h (congrArg Prod.fst hne)
    · exact h (congrArg Prod.snd hne)
  · rintro ⟨x, p, hp, hb, hb', habove⟩
    refine ⟨(x, p), hp, hb, hb', fun v hv hle hne => ?_⟩
    refine habove v.1 v.2 hv ⟨hle, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hne (Prod.ext hcon.1 hcon.2)

end Compare

/-! ### Membership -/

section Membership

open Classical in
/-- **Job sequencing is `Σ₁`-definable**: guess the schedule, the late jobs,
the completion times along the schedule and the penalty total of the late
jobs, and check first-order that both are ripple-carry additions, that a job
is late exactly when its completion time exceeds its deadline, and that the
penalty total does not exceed the bound. Since NP is defined as
`Σ₁`-definability, this is the membership half of job sequencing. -/
theorem jobSequencing_sigmaSODefinable : SigmaSODefinable 1 JobSequencing := by
  refine ⟨[jobSeqGuessBlock], rfl, jobSequencingKernel, ?_⟩
  intro A _ _ _
  constructor
  · -- a good schedule yields a certificate: two walks and the late jobs
    rintro ⟨hfin, hlin, sched, hslin, hpen⟩
    obtain ⟨a₀, -, h₀'⟩ := exists_minPos (Le := JSLe (A := A)) (Posn := fun _ => True) hlin
      ⟨Classical.arbitrary A, trivial⟩
    have h₀ : ∀ y : A, JSLe a₀ y := fun y => h₀' y trivial
    have hwlin : IsLinOrd (wideLe (JSLe (A := A))) := isLinOrd_wideLe hlin
    have hwt : ∀ (s : Bool) (i : A),
        binNum (wideLe JSLe) (WidePosn JSPosn) (JWt s i) = JVal s i :=
      fun s i => binNum_jWt hlin h₀ s i
    have hbound : ∀ (s : Bool) (T : A → Prop),
        (∑ᶠ j ∈ {j : A | T j}, binNum (wideLe JSLe) (WidePosn JSPosn) (JWt s j)) <
          2 ^ ({u : A × A | WidePosn JSPosn u} : Set (A × A)).ncard := by
      intro s T
      have hcongr : (∑ᶠ j ∈ {j : A | T j},
            binNum (wideLe JSLe) (WidePosn JSPosn) (JWt s j)) =
          ∑ᶠ j ∈ {j : A | T j}, binNum JSLe JSPosn (JBit s j) :=
        finsum_mem_congr rfl fun j _ => by rw [JWt, binNum_jWide hlin h₀]
      rw [hcongr]
      exact finsum_binNum_lt_wide hlin (JBit s) {j : A | T j}
    obtain ⟨PS1, Cy1, hchain1⟩ := exists_chain (ILe := sched) (IItem := JSJob)
      (PLe := wideLe JSLe) (PPosn := WidePosn JSPosn) (S := JSJob) (wt := JWt true)
      hslin hwlin (fun _ hi => hi) (hbound true JSJob)
    obtain ⟨PS0, Cy0, hchain0⟩ := exists_chain (ILe := JSLe (A := A)) (IItem := JSJob)
      (PLe := wideLe JSLe) (PPosn := WidePosn JSPosn)
      (S := fun j => JSJob j ∧ JSLate sched j) (wt := JWt false)
      hlin hwlin (fun _ hi => hi.1) (hbound false _)
    refine ⟨fun idx => match idx with
      | .sched => fun w : Fin 2 → A => sched (w 0) (w 1)
      | .late => fun w : Fin 1 → A => JSJob (w 0) ∧ JSLate sched (w 0)
      | .ps s => fun w : Fin 3 → A =>
          (match s with | true => PS1 | false => PS0) (w 0) (w 1, w 2)
      | .cy s => fun w : Fin 3 → A =>
          (match s with | true => Cy1 | false => Cy0) (w 0) (w 1, w 2), ?_⟩
    refine (realize_jobSequencingKernel _).mpr
      ⟨⟨hlin, hslin⟩, fun j hj => hj.1, fun s => ?_, ?_, ?_⟩
    · cases s
      · exact ⟨fun i x p hi hp => hchain0.1 i (x, p) hi hp,
          fun i j x p hij hp => hchain0.2.1 i j (x, p) hij hp,
          fun i j x p y q hij hpq =>
            hchain0.2.2.1 i j (x, p) (y, q) hij ((succPos_wide hlin).mpr hpq),
          fun i j x p hij hp =>
            hchain0.2.2.2.1 i j (x, p) hij ((minPos_wide hlin).mpr hp),
          fun i j x p hij hp =>
            hchain0.2.2.2.2 i j (x, p) hij ((maxPos_wide hlin).mpr hp)⟩
      · exact ⟨fun i x p hi hp => hchain1.1 i (x, p) hi hp,
          fun i j x p hij hp => hchain1.2.1 i j (x, p) hij hp,
          fun i j x p y q hij hpq =>
            hchain1.2.2.1 i j (x, p) (y, q) hij ((succPos_wide hlin).mpr hpq),
          fun i j x p hij hp =>
            hchain1.2.2.2.1 i j (x, p) hij ((minPos_wide hlin).mpr hp),
          fun i j x p hij hp =>
            hchain1.2.2.2.2 i j (x, p) hij ((maxPos_wide hlin).mpr hp)⟩
    · -- a job is late exactly when its completion time exceeds its deadline
      intro j hj
      have hcompl : binNum (wideLe JSLe) (WidePosn JSPosn) (PS1 j) =
          JSCompletion sched j := by
        rw [chain_sound hslin hwlin (fun _ hi => hi) hchain1 j hj]
        exact finsum_mem_congr rfl fun i _ => hwt true i
      refine Iff.trans ?_ (binNum_wide_lt_iff hlin (JDlineW j) (PS1 j))
      rw [binNum_jDlineW hlin h₀, hcompl]
      exact ⟨fun h => h.2, fun h => ⟨hj, h⟩⟩
    · -- the penalty total does not exceed the bound
      intro j hjmax
      have hps : binNum (wideLe JSLe) (WidePosn JSPosn) (PS0 j) = JSPenalty sched := by
        rw [chain_sound hlin hwlin (fun _ hi => hi.1) hchain0 j hjmax.1,
          partSum_max (fun _ hi => hi.1) hjmax]
        exact finsum_mem_congr rfl fun i _ => hwt false i
      intro hex
      have hlt := (binNum_wide_lt_iff hlin JBndW (PS0 j)).mpr hex
      rw [binNum_jBndW hlin h₀, hps] at hlt
      exact absurd hpen (Nat.not_le.mpr hlt)
  · -- a certificate yields a good schedule: both walks are sound
    rintro ⟨ρ, hρ⟩
    obtain ⟨⟨hlin, hslin⟩, hlatejob, hwalk, hldef, hfin⟩ :=
      (realize_jobSequencingKernel ρ).mp hρ
    obtain ⟨a₀, -, h₀'⟩ := exists_minPos (Le := JSLe (A := A)) (Posn := fun _ => True) hlin
      ⟨Classical.arbitrary A, trivial⟩
    have h₀ : ∀ y : A, JSLe a₀ y := fun y => h₀' y trivial
    have hwlin : IsLinOrd (wideLe (JSLe (A := A))) := isLinOrd_wideLe hlin
    have hwt : ∀ (s : Bool) (i : A),
        binNum (wideLe JSLe) (WidePosn JSPosn) (JWt s i) = JVal s i :=
      fun s i => binNum_jWt hlin h₀ s i
    have hchain : ∀ s : Bool, IsChain (JOrd ρ s) JSJob (wideLe JSLe) (WidePosn JSPosn)
        (JSel ρ s) (JWt s) (JPS ρ s) (JCy ρ s) :=
      fun s => ⟨fun i u hi hp => (hwalk s).1 i u.1 u.2 hi hp,
        fun i j u hij hp => (hwalk s).2.1 i j u.1 u.2 hij hp,
        fun i j u v hij hpq =>
          (hwalk s).2.2.1 i j u.1 u.2 v.1 v.2 hij ((succPos_wide hlin).mp hpq),
        fun i j u hij hp => (hwalk s).2.2.2.1 i j u.1 u.2 hij ((minPos_wide hlin).mp hp),
        fun i j u hij hp => (hwalk s).2.2.2.2 i j u.1 u.2 hij ((maxPos_wide hlin).mp hp)⟩
    -- the guessed late jobs are the jobs the schedule leaves late
    have hlate : ∀ j : A, JSJob j → (JLate ρ j ↔ JSLate (JSched ρ) j) := by
      intro j hj
      have hcompl : binNum (wideLe JSLe) (WidePosn JSPosn) (JPS ρ true j) =
          JSCompletion (JSched ρ) j := by
        rw [chain_sound hslin hwlin (fun _ hi => hi) (hchain true) j hj]
        exact finsum_mem_congr rfl fun i _ => hwt true i
      rw [hldef j hj, ← binNum_wide_lt_iff hlin (JDlineW j) (JPS ρ true j),
        binNum_jDlineW hlin h₀, hcompl]
      exact Iff.rfl
    have hset : {j : A | JSel ρ false j} =
        {j : A | JSJob j ∧ JSLate (JSched ρ) j} := by
      ext j
      exact ⟨fun h => ⟨hlatejob j h, (hlate j (hlatejob j h)).mp h⟩,
        fun h => (hlate j h.1).mpr h.2⟩
    refine ⟨‹Finite A›, hlin, JSched ρ, hslin, ?_⟩
    by_cases hjobs : ∃ j : A, JSJob j
    · obtain ⟨jmax, hjmax⟩ := exists_maxPos hlin hjobs
      have hps : binNum (wideLe JSLe) (WidePosn JSPosn) (JPS ρ false jmax) =
          JSPenalty (JSched ρ) := by
        rw [chain_sound hlin hwlin hlatejob (hchain false) jmax hjmax.1,
          partSum_max hlatejob hjmax, JSPenalty, ← hset]
        exact finsum_mem_congr rfl fun i _ => hwt false i
      have := hfin jmax hjmax
      rw [← binNum_wide_lt_iff hlin JBndW (JPS ρ false jmax), binNum_jBndW hlin h₀,
        hps] at this
      exact Nat.not_lt.mp this
    · have hno : ∀ j : A, ¬JSJob j := fun j hj => hjobs ⟨j, hj⟩
      have hempty : {j : A | JSJob j ∧ JSLate (JSched ρ) j} = (∅ : Set A) := by
        ext j
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hno j h.1
      rw [JSPenalty, hempty, finsum_mem_empty]
      exact Nat.zero_le _

end Membership

end SigmaOne

end DescriptiveComplexity
