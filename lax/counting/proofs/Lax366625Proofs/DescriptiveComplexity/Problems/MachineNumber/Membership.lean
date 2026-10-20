/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax366625Proofs.DescriptiveComplexity.Problems.MachineNumber.Defs
import Lax366625Proofs.DescriptiveComplexity.Problems.Machine.Fixpoint
import Lax366625Proofs.DescriptiveComplexity.Problems.CircuitNumber.Membership
import Lax366625.CountingProblems
import Lax366625.CountingRuns
import Lax366625.CountingSat
import Lax366625.HornNumbers
import Lax366625.MachineNumbers
import Lax366625.NumberedCircuits
import Lax366625.QuantitativeLogic
import Lax366625.SecondOrderCounting
import Lax366625.WitnessCounting
import Lax485149.Complement
import Lax485149.DeterministicReachability
import Lax485149.DeterministicTransitiveClosure
import Lax485149.FirstOrderDefinability
import Lax485149.HeadAutomata
import Lax485149.KromFragment
import Lax485149.Reachability
import Lax485149.SecondOrderAtoms
import Lax485149.TransitiveClosure
import Lax485149.TwoSat
import Lax535992.CircuitValue
import Lax535992.DeterministicMachines
import Lax535992.Game
import Lax535992.HornFragment
import Lax535992.HornSat
import Lax535992.InflationaryFixedPoint
import Lax535992.LeastFixedPoint
import Lax895169.ArithmeticLogic
import Lax895169.BitLogic
import Lax895169.BitPredicate
import Lax895169.LogTimeMachines
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax366625.MachineNumbers
end Lax366625.MachineNumbers

namespace Lax366625.MachineNumbers.TMData
end Lax366625.MachineNumbers.TMData

namespace Lax366625.QuantitativeLogic
end Lax366625.QuantitativeLogic

namespace Lax535992.DeterministicMachines.TMData
end Lax535992.DeterministicMachines.TMData

namespace Lax535992.HornFragment
end Lax535992.HornFragment

namespace Lax535992.LeastFixedPoint
end Lax535992.LeastFixedPoint

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.QuantitativeLogic (FPDefinable QLFPDef QTerm)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax366625.MachineNumbers (LowerCell OutDigit cellRank machineNumber mnLe mnOne mnOut)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax904597.Machines (Config SuccPos TMAcc TMDst TMLe TMPosn TMRead TMRight TMSrc TMTr TMWrite tmData)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.HornFragment (HornClause)
end Lax366625Proofs.DescriptiveComplexity

namespace Lax366625Proofs.DescriptiveComplexity
export Lax535992.LeastFixedPoint (Derives lfpAssign)
end Lax366625Proofs.DescriptiveComplexity

namespace FirstOrder.Language
export Lax366625.MachineNumbers (turingOut)
end FirstOrder.Language

namespace FirstOrder.Language
export Lax904597.Machines (turing)
end FirstOrder.Language

namespace Lax904597.Machines.TMData
export Lax366625.MachineNumbers.TMData (Halts)
end Lax904597.Machines.TMData

namespace Lax904597.Machines.TMData
export Lax535992.DeterministicMachines.TMData (Deterministic)
end Lax904597.Machines.TMData

/-!
# The number written by a machine is in FP

`DescriptiveComplexity.dtmNumber_mem_FP`: a definition in QFO(LFP) of
`DescriptiveComplexity.DTMNumber`.

* The fixed point is the one of deterministic machine acceptance
  (`DescriptiveComplexity.DTFix.dtRules`): the state, the head and the tape of
  the run, indexed by the time positions.
* The machine halts at a time whose configuration admits no step, and accepts
  when the state there is accepting: a first-order condition on the fixed
  point
  (`DescriptiveComplexity.MachNum.halted_iff`); a negation, which the output of
  a definition in QFO(LFP) is free to use.
* The output is the term
  `Σp. [p is an output cell holding a one at the halting time] · Πq. ([q is an
  output cell before p on the tape] + 1)`, as for the number written by a
  circuit.
-/

namespace Lax366625Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure DTFix

namespace MachNum

/-! ### Halting, read off the fixed point -/

section Halted

variable {A : Type} [Lax904597.Machines.turing.Structure A] [LinearOrder A] [Finite A]

/-- Some transition applies in the state `q` to the symbol `a` with the head
at `h`, and can fire. -/
def Core (q h a : A) : Prop :=
  ∃ τ, Lax904597.Machines.TMTr τ ∧ Lax904597.Machines.TMSrc τ q ∧ Lax904597.Machines.TMRead τ a ∧ (∃ q', Lax904597.Machines.TMDst τ q') ∧ (∃ a', Lax904597.Machines.TMWrite τ a') ∧
    ((Lax904597.Machines.TMRight τ ∧ ∃ p, Lax904597.Machines.SuccPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn h p) ∨ (¬Lax904597.Machines.TMRight τ ∧ ∃ p, Lax904597.Machines.SuccPos Lax904597.Machines.TMLe Lax904597.Machines.TMPosn p h))

/-- **The halting configuration, in the fixed point**: a cell holds a symbol
when the machine halts exactly when the fixed point has a time whose
configuration admits no step and whose tape holds that symbol there. -/
theorem halted_iff (hwf : (Lax904597.Machines.tmData A).WellFormed) (hdet : (Lax904597.Machines.tmData A).Deterministic)
    (p s : A) :
    (∃ t q h a : A, DQ t q ∧ DH t h ∧ DT t h a ∧ ¬Core q h a ∧ Lax904597.Machines.TMAcc q ∧ DT t p s) ↔
      ∃ c : Lax904597.Machines.Config A, (Lax904597.Machines.tmData A).Halts c ∧ (Lax904597.Machines.tmData A).Acc c.state ∧ c.tape p = s := by
  constructor
  · rintro ⟨t, q, h, a, hQ, hH, hT, hcore, hacc, hTp⟩
    obtain ⟨ht, c₀, c, hinit, hrun, hstate⟩ := derives_sound hwf hdet hQ
    have hhead : c.head = h := (derives_sound hwf hdet hH).2 c₀ c hinit hrun
    have htape : c.tape h = a := (derives_sound hwf hdet hT).2 c₀ c hinit hrun
    have htp : c.tape p = s := (derives_sound hwf hdet hTp).2 c₀ c hinit hrun
    refine ⟨c, ⟨c₀, _, hinit, bitRank_lt_card ht, hrun, fun e he => hcore ?_⟩,
      hstate ▸ hacc, htp⟩
    have := (TMData.exists_step_iff (M := Lax904597.Machines.tmData A) c).mp ⟨e, he⟩
    rwa [hstate, hhead, htape] at this
  · rintro ⟨c, ⟨c₀, n, hinit, hn, hrun, hstuck⟩, hacc, rfl⟩
    obtain ⟨t, ht, hrk⟩ := exists_pos_bitRank hwf.1 n hn
    obtain ⟨hQ, hH, hT⟩ := derivedAt_of_run hwf hinit n t ht hrk c hrun
    exact ⟨t, c.state, c.head, c.tape c.head, hQ, hH, hT c.head,
      fun hcore => (not_exists.mpr hstuck) ((TMData.exists_step_iff (M := Lax904597.Machines.tmData A) c).mpr hcore),
      hacc, hT p⟩

end Halted

/-! ### The definition -/

/-- The vocabulary of the rules: machines writing a number, with the order. -/
abbrev numLang : Language := Lax366625.MachineNumbers.turingOut.sum Language.order

/-- The vocabulary of the rules of machine acceptance, read in the one of the
rules here. -/
def ordHom : tmOrd →ᴸ numLang :=
  LHom.sumMap LHom.sumInl (LHom.id Language.order)

instance ordHom_isExpansionOn (A : Type) [Lax366625.MachineNumbers.turingOut.Structure A] [LinearOrder A] :
    ordHom.IsExpansionOn A where
  map_onFunction := fun {_} f _ => isEmptyElim f
  map_onRelation := fun {_} R _ => by cases R <;> rfl

/-- The rules of the run, over the larger vocabulary. -/
noncomputable def numRules : List (Lax535992.HornFragment.HornClause numLang dtBlock 9) :=
  dtRules.map (HornClause.onLang ordHom)

/-- The vocabulary of the output: the rules', and the relations of the run. -/
abbrev outLang : Language := numLang.sum dtBlock.lang

/-- The vocabulary of the guards, read in the one of the output. -/
def outHom : tmOrd →ᴸ outLang :=
  LHom.sumInl.comp ordHom

section Formulas

variable {γ : Type}

/-- “Is an output cell”. -/
noncomputable def outA (x : γ) : outLang.Formula γ :=
  Relations.formula₁ (Sum.inl (Sum.inl Lax366625.MachineNumbers.mnOut) : outLang.Relations 1) (Term.var x)

/-- “Is read as the digit `1`”. -/
noncomputable def oneA (x : γ) : outLang.Formula γ :=
  Relations.formula₁ (Sum.inl (Sum.inl Lax366625.MachineNumbers.mnOne) : outLang.Relations 1) (Term.var x)

/-- The order of the tape. -/
noncomputable def leA (x y : γ) : outLang.Formula γ :=
  Relations.formula₂ (Sum.inl (Sum.inl Lax366625.MachineNumbers.mnLe) : outLang.Relations 2) (Term.var x) (Term.var y)

/-- The state of the run at a time. -/
noncomputable def qA (t q : γ) : outLang.Formula γ :=
  Relations.formula₂ (Sum.inr ⟨some true, rfl⟩ : outLang.Relations 2) (Term.var t) (Term.var q)

/-- The head of the run at a time. -/
noncomputable def hA (t h : γ) : outLang.Formula γ :=
  Relations.formula₂ (Sum.inr ⟨some false, rfl⟩ : outLang.Relations 2) (Term.var t) (Term.var h)

/-- The tape of the run at a time. -/
noncomputable def tA (t p a : γ) : outLang.Formula γ :=
  Relations.formula (Sum.inr ⟨none, rfl⟩ : outLang.Relations 3)
    ![Term.var t, Term.var p, Term.var a]

/-- “Is an accepting state”. -/
noncomputable def accA (x : γ) : outLang.Formula γ :=
  outHom.onFormula (accG x)

/-- Some transition applies and can fire. -/
noncomputable def coreF (q h a : γ) : outLang.Formula γ :=
  Formula.iExs (Fin 1) (outHom.onFormula
    (((((trG (Sum.inr 0) ⊓ srcG (Sum.inr 0) (Sum.inl q)) ⊓ readG (Sum.inr 0) (Sum.inl a)) ⊓
      existsDstG (Sum.inr 0)) ⊓ existsWriteG (Sum.inr 0)) ⊓ canMoveG (Sum.inr 0) (Sum.inl h)))

/-- “The instance is a well-formed deterministic machine, and `p` is an output
cell holding a one when it halts.” -/
noncomputable def digitF : outLang.Formula (Empty ⊕ Fin 1) :=
  (Formula.relabel (fun e : Empty => e.elim) (outHom.onSentence (wfS ⊓ detS)) ⊓
      outA (Sum.inr 0)) ⊓
    Formula.iExs (Fin 5)
      ((((((qA (Sum.inr 0) (Sum.inr 1) ⊓ hA (Sum.inr 0) (Sum.inr 2)) ⊓
        tA (Sum.inr 0) (Sum.inr 2) (Sum.inr 3)) ⊓
        ∼(coreF (Sum.inr 1) (Sum.inr 2) (Sum.inr 3))) ⊓ accA (Sum.inr 1)) ⊓
        tA (Sum.inr 0) (Sum.inl (Sum.inr 0)) (Sum.inr 4)) ⊓ oneA (Sum.inr 4))

/-- “`q` is an output cell strictly before `p`”. -/
noncomputable def lowF : outLang.Formula ((Empty ⊕ Fin 1) ⊕ Fin 1) :=
  (outA (Sum.inr 0) ⊓ ∼(Term.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inl (Sum.inr 0))))) ⊓
    leA (Sum.inr 0) (Sum.inl (Sum.inr 0))

end Formulas

/-- **The output term.** -/
noncomputable def numOut : Lax366625.QuantitativeLogic.QTerm outLang Empty :=
  .sum 1 (.mul (.ind digitF) (.prod 1 (.add (.ind lowF) (.const 1))))

/-- The definition of the number written by a machine in QFO(LFP). -/
noncomputable def numDef : Lax366625.QuantitativeLogic.QLFPDef Lax366625.MachineNumbers.turingOut where
  B := dtBlock
  k := 9
  rules := numRules
  out := numOut

/-! ### The value of the definition -/

section Value

variable {A : Type} [Lax366625.MachineNumbers.turingOut.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- The structure the output is read in. -/
abbrev outStr (A : Type) [Lax366625.MachineNumbers.turingOut.Structure A] [LinearOrder A] :
    outLang.Structure A :=
  @sumStructure _ _ A _ (dtBlock.structure (Lax535992.LeastFixedPoint.lfpAssign (A := A) numRules))

instance outHom_isExpansionOn :
    @LHom.IsExpansionOn _ _ outHom A _ (outStr A) :=
  @LHom.IsExpansionOn.mk _ _ outHom A _ (outStr A) (fun {_} f _ => isEmptyElim f)
    (fun {_} R _ => by cases R <;> rfl)

variable {γ : Type} (v : γ → A)

omit [Finite A] [Nonempty A] in
theorem lfp_numRules (i : dtBlock.ι) (x : Fin (dtBlock.arity i) → A) :
    Lax535992.LeastFixedPoint.lfpAssign (A := A) numRules i x ↔ Lax535992.LeastFixedPoint.Derives (A := A) dtRules ⟨i, x⟩ :=
  derives_onLang ordHom dtRules ⟨i, x⟩

omit [Finite A] [Nonempty A] in
theorem realize_qA (t q : γ) :
    (@Formula.Realize _ A (outStr A) _ (qA t q) v) ↔ DQ (v t) (v q) := by
  let := outStr A
  refine Formula.realize_rel₂.trans ?_
  exact (lfp_numRules (some true) _).trans (iff_of_eq (congrArg
    (fun w => Lax535992.LeastFixedPoint.Derives (A := A) dtRules ⟨some true, w⟩) (funext fun j => by fin_cases j <;> rfl)))

omit [Finite A] [Nonempty A] in
theorem realize_hA (t h : γ) :
    (@Formula.Realize _ A (outStr A) _ (hA t h) v) ↔ DH (v t) (v h) := by
  let := outStr A
  refine Formula.realize_rel₂.trans ?_
  exact (lfp_numRules (some false) _).trans (iff_of_eq (congrArg
    (fun w => Lax535992.LeastFixedPoint.Derives (A := A) dtRules ⟨some false, w⟩) (funext fun j => by fin_cases j <;> rfl)))

omit [Finite A] [Nonempty A] in
theorem realize_tA (t p a : γ) :
    (@Formula.Realize _ A (outStr A) _ (tA t p a) v) ↔ DT (v t) (v p) (v a) := by
  let := outStr A
  refine Formula.realize_rel.trans ?_
  exact (lfp_numRules none _).trans (iff_of_eq (congrArg
    (fun w => Lax535992.LeastFixedPoint.Derives (A := A) dtRules ⟨none, w⟩) (funext fun j => by fin_cases j <;> rfl)))

omit [Finite A] [Nonempty A] in
theorem realize_outA (x : γ) :
    (@Formula.Realize _ A (outStr A) _ (outA x) v) ↔ RelMap Lax366625.MachineNumbers.mnOut ![v x] := by
  let := outStr A
  exact Formula.realize_rel₁

omit [Finite A] [Nonempty A] in
theorem realize_oneA (x : γ) :
    (@Formula.Realize _ A (outStr A) _ (oneA x) v) ↔ RelMap Lax366625.MachineNumbers.mnOne ![v x] := by
  let := outStr A
  exact Formula.realize_rel₁

omit [Finite A] [Nonempty A] in
theorem realize_leA (x y : γ) :
    (@Formula.Realize _ A (outStr A) _ (leA x y) v) ↔ RelMap Lax366625.MachineNumbers.mnLe ![v x, v y] := by
  let := outStr A
  exact Formula.realize_rel₂

omit [Finite A] [Nonempty A] in
theorem realize_accA (x : γ) :
    (@Formula.Realize _ A (outStr A) _ (accA x) v) ↔ Lax904597.Machines.TMAcc (v x) := by
  let := outStr A
  exact (LHom.realize_onFormula outHom _).trans (realize_accG x)

omit [Finite A] [Nonempty A] in
theorem realize_coreF (q h a : γ) :
    (@Formula.Realize _ A (outStr A) _ (coreF q h a) v) ↔ Core (v q) (v h) (v a) := by
  let := outStr A
  rw [coreF, Formula.realize_iExs]
  constructor
  · rintro ⟨i, hi⟩
    rw [LHom.realize_onFormula] at hi
    simp only [Formula.realize_inf, realize_trG, realize_srcG, realize_readG,
      realize_existsDstG, realize_existsWriteG, realize_canMoveG, Sum.elim_inl,
      Sum.elim_inr] at hi
    exact ⟨i 0, hi.1.1.1.1.1, hi.1.1.1.1.2, hi.1.1.1.2, hi.1.1.2, hi.1.2, hi.2⟩
  · rintro ⟨τ, h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun _ => τ, ?_⟩
    rw [LHom.realize_onFormula]
    simp only [Formula.realize_inf, realize_trG, realize_srcG, realize_readG,
      realize_existsDstG, realize_existsWriteG, realize_canMoveG, Sum.elim_inl,
      Sum.elim_inr]
    exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

omit [Nonempty A] in
theorem realize_digitF (w : Fin 1 → A) :
    (@Formula.Realize _ A (outStr A) _ digitF (Sum.elim default w)) ↔
      ((Lax904597.Machines.tmData A).WellFormed ∧ (Lax904597.Machines.tmData A).Deterministic) ∧ Lax366625.MachineNumbers.OutDigit (w 0) := by
  have hq := fun (v : (Empty ⊕ Fin 1) ⊕ Fin 5 → A) => realize_qA v (Sum.inr 0) (Sum.inr 1)
  have hh := fun (v : (Empty ⊕ Fin 1) ⊕ Fin 5 → A) => realize_hA v (Sum.inr 0) (Sum.inr 2)
  have ht := fun (v : (Empty ⊕ Fin 1) ⊕ Fin 5 → A) =>
    realize_tA v (Sum.inr 0) (Sum.inr 2) (Sum.inr 3)
  have hc := fun (v : (Empty ⊕ Fin 1) ⊕ Fin 5 → A) =>
    realize_coreF v (Sum.inr 1) (Sum.inr 2) (Sum.inr 3)
  have htp := fun (v : (Empty ⊕ Fin 1) ⊕ Fin 5 → A) =>
    realize_tA v (Sum.inr 0) (Sum.inl (Sum.inr 0)) (Sum.inr 4)
  have ho := fun (v : (Empty ⊕ Fin 1) ⊕ Fin 5 → A) => realize_oneA v (Sum.inr 4)
  have hacc := fun (v : (Empty ⊕ Fin 1) ⊕ Fin 5 → A) => realize_accA v (Sum.inr 1)
  have hout := realize_outA (Sum.elim default w : Empty ⊕ Fin 1 → A) (Sum.inr 0)
  let := outStr A
  have hguard : (Formula.relabel (fun e : Empty => e.elim)
      (outHom.onSentence (wfS ⊓ detS)) : outLang.Formula (Empty ⊕ Fin 1)).Realize
        (Sum.elim default w) ↔ (Lax904597.Machines.tmData A).WellFormed ∧ (Lax904597.Machines.tmData A).Deterministic := by
    rw [Formula.realize_relabel]
    refine (iff_of_eq (congrArg _ (Subsingleton.elim _ default))).trans ?_
    refine (LHom.realize_onSentence (φ := outHom) A (wfS ⊓ detS)).trans ?_
    exact Formula.realize_inf.trans (and_congr realize_wfS realize_detS)
  rw [digitF, Formula.realize_inf, Formula.realize_inf, hguard, and_assoc]
  refine and_congr_right fun hwd => ?_
  refine and_congr hout (Formula.realize_iExs.trans ?_)
  constructor
  · rintro ⟨i, hi⟩
    simp only [Formula.realize_inf, Formula.realize_not, hq, hh, ht, hc, htp, ho, hacc] at hi
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, ha⟩, h5⟩, h6⟩ := hi
    obtain ⟨c, hc', hca, hs⟩ :=
      (halted_iff hwd.1 hwd.2 (w 0) (i 4)).mp ⟨_, _, _, _, h1, h2, h3, h4, ha, h5⟩
    exact ⟨c, hc', hca, hs ▸ h6⟩
  · rintro ⟨c, hc', hca, h1⟩
    obtain ⟨t, q, h, a, h1', h2, h3, h4, ha, h5⟩ :=
      (halted_iff hwd.1 hwd.2 (w 0) (c.tape (w 0))).mpr ⟨c, hc', hca, rfl⟩
    refine ⟨![t, q, h, a, c.tape (w 0)], ?_⟩
    simp only [Formula.realize_inf, Formula.realize_not, hq, hh, ht, hc, htp, ho, hacc]
    exact ⟨⟨⟨⟨⟨⟨h1', h2⟩, h3⟩, h4⟩, ha⟩, h5⟩, h1⟩

omit [Finite A] [Nonempty A] in
theorem realize_lowF (w u : Fin 1 → A) :
    (@Formula.Realize _ A (outStr A) _ lowF (Sum.elim (Sum.elim default w) u)) ↔
      Lax366625.MachineNumbers.LowerCell (w 0) (u 0) := by
  have h1 := realize_outA (Sum.elim (Sum.elim default w) u : (Empty ⊕ Fin 1) ⊕ Fin 1 → A)
    (Sum.inr 0)
  have h2 := realize_leA (Sum.elim (Sum.elim default w) u : (Empty ⊕ Fin 1) ⊕ Fin 1 → A)
    (Sum.inr 0) (Sum.inl (Sum.inr 0))
  let := outStr A
  exact (Formula.realize_inf.trans (and_congr (Formula.realize_inf.trans (and_congr h1
    (Formula.realize_not.trans (not_congr Formula.realize_equal)))) h2)).trans and_assoc

omit [Nonempty A] in
open Classical in
/-- **The definition computes the number written by the machine.** -/
theorem numDef_value : numDef.value A = Lax366625.MachineNumbers.machineNumber A := by
  let := outStr A
  have hprod : ∀ w : Fin 1 → A,
      ∏ᶠ u : Fin 1 → A, ((if Lax366625.MachineNumbers.LowerCell (w 0) (u 0) then 1 else 0) + 1) = 2 ^ Lax366625.MachineNumbers.cellRank (w 0) :=
    fun w => (finprod_comp_equiv (Equiv.funUnique (Fin 1) A)
      (f := fun q => (if Lax366625.MachineNumbers.LowerCell (w 0) q then 1 else 0) + 1)).trans
        (finprod_boole_add_one _)
  rw [Lax366625.QuantitativeLogic.QLFPDef.value, Lax366625.QuantitativeLogic.QTerm.value, Lax366625.MachineNumbers.machineNumber]
  change (numOut.eval (A := A) default) = _
  simp only [numOut, Lax366625.QuantitativeLogic.QTerm.eval, realize_digitF, realize_lowF, hprod, ite_mul, one_mul,
    zero_mul]
  by_cases hwd : (Lax904597.Machines.tmData A).WellFormed ∧ (Lax904597.Machines.tmData A).Deterministic
  · simp only [hwd, true_and, ite_true]
    exact finsum_comp_equiv (Equiv.funUnique (Fin 1) A)
      (f := fun p => if Lax366625.MachineNumbers.OutDigit p then 2 ^ Lax366625.MachineNumbers.cellRank p else 0)
  · simp only [hwd, false_and, ite_false]
    exact finsum_zero

end Value

end MachNum

/-- **The number written by a machine is definable in QFO(LFP).** -/
theorem dtmNumber_fpDefinable : Lax366625.QuantitativeLogic.FPDefinable DTMNumber :=
  ⟨MachNum.numDef, fun _A _ _ _ _ => MachNum.numDef_value.symm⟩

/-- **The number written by a deterministic machine is in FP.** -/
theorem dtmNumber_mem_FP : DTMNumber ∈ FP :=
  dtmNumber_fpDefinable

end Lax366625Proofs.DescriptiveComplexity


