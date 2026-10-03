import Lax904597.NPClass
import Lax624099.Problems
import Lax624099.ValueInvention
import Lax624099.ClassRE
import Lax624099.FiniteSatisfiability
import Lax624099.Halting
import Lax624099.CodeHalting
import Lax624099.PostCorrespondence
import Lax624099.ConcreteInstances
import Lax624099.FiniteSatisfiabilityInvariance
import Lax624099.HaltingInvariance
import Lax624099.CodeHaltingInvariance
import Lax624099.PostCorrespondenceInvariance
import Lax624099.REClosure
import Lax624099.REFinite
import Lax624099.NPSubsetRE
import Lax624099.FinsatREComplete
import Lax624099.CodehaltREComplete
import Lax624099.HaltREComplete
import Lax624099.PcpREComplete
import Lax624099.REIsRecursivelyEnumerable
import Lax624099.ReductionsComputable
import Lax624099.REHardUndecidable
import Lax624099.Trakhtenbrot
import Lax624099.HaltingUndecidable
import Lax624099.PcpUndecidable
import Lax624099.RENeCoRE
import Lax624099Proofs.DescriptiveComplexity.RecursivelyEnumerable
import Lax624099Proofs.DescriptiveComplexity.Problems.FinSat
import Lax624099Proofs.DescriptiveComplexity.Problems.Machine.HaltHard
import Lax624099Proofs.DescriptiveComplexity.Computability.CodeHaltComplete
import Lax624099Proofs.DescriptiveComplexity.Computability.PcpComplete
import Lax624099Proofs.DescriptiveComplexity.Computability.Catalog
import Lax624099Proofs.DescriptiveComplexity.Computability.Reduction

/-!
# The recursive-enumerability statements, from the library's theorems

Each claim is proved from the library's theorem of the same name, transported
along the agreement between the library's bundled problem and the concept's,
which the invariance of the property gives. The completeness proofs assume
the submission's own statements where the library's proofs compose: Trakhtenbrot's
reduction makes FINSAT hard, every semi-decidable problem reduces to HALT and to
CODEHALT, and the computation-history dominoes carry hardness from HALT to PCP;
undecidability follows from hardness through the computability of reductions.
-/

namespace Lax624099Proofs.Bridge

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes
open Lax904597.Machines Lax624099.Problems
open Lax624099.ValueInvention Lax624099.ClassRE Lax624099.FiniteSatisfiability Lax624099.Halting
open Lax624099.CodeHalting Lax624099.PostCorrespondence Lax624099.ConcreteInstances
open Lax624099.FiniteSatisfiabilityInvariance Lax624099.HaltingInvariance
open Lax624099.CodeHaltingInvariance Lax624099.PostCorrespondenceInvariance
open Lax624099.REClosure Lax624099.REFinite Lax624099.FinsatREComplete Lax624099.CodehaltREComplete
open Lax624099.HaltREComplete Lax624099.PcpREComplete Lax624099.REIsRecursivelyEnumerable
open Lax624099.REHardUndecidable Lax624099.RENeCoRE

/-- For an invariant property, the problem it gives holds exactly where the
property does. -/
theorem ofPred_iff {L : Language.{0, 0}} [L.IsRelational] {P : ∀ (A : Type) [L.Structure A], Prop}
    (hP : ∀ {A B : Type} [L.Structure A] [L.Structure B], (A ≃[L] B) → (P A ↔ P B))
    (V : Type) [L.Structure V] : DecisionProblem.ofPred P V ↔ P V := by
  constructor
  · rintro ⟨B, i, f, h⟩
    exact (hP f).mp h
  · intro h
    exact ⟨V, inferInstance, Language.Equiv.refl _ _, h⟩

/-- An ordered first-order reduction transported along agreements of its two
ends. -/
def OrderedFOReduction.congr {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P P' : DecisionProblem L} {Q Q' : DecisionProblem L'}
    (hP : ∀ (A : Type) [L.Structure A], P A ↔ P' A) (hQ : ∀ (A : Type) [L'.Structure A], Q A ↔ Q' A)
    (f : OrderedFOReduction P Q) : OrderedFOReduction P' Q' :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ _ => ((hP A).symm.trans (f.correct A)).trans (hQ _) }

/-! ### The problems: invariance, characterization, agreement -/

/--
---
conclusion: Lax624099.FiniteSatisfiabilityInvariance.finSatOn_iso
---
The library's invariance theorem for finite satisfiability.
-/
theorem finSatOn_iso {A B : Type} [finsat.Structure A] [finsat.Structure B] (e : A ≃[finsat] B) :
    FinSat.FinSatOn A ↔ FinSat.FinSatOn B :=
  ⟨DescriptiveComplexity.FinSat.finSatOn_map e, DescriptiveComplexity.FinSat.finSatOn_map e.symm⟩

/--
---
conclusion: Lax624099.FiniteSatisfiabilityInvariance.finsat_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem finsat_iff (A : Type) [finsat.Structure A] : FINSAT A ↔ FinSat.FinSatOn A :=
  ofPred_iff @finSatOn_iso A

/-- The library's bundled FINSAT and the concept's agree on every instance. -/
theorem finsat_agree (A : Type) [finsat.Structure A] : DescriptiveComplexity.FINSAT A ↔ FINSAT A :=
  (finsat_iff A).symm

/--
---
conclusion: Lax624099.HaltingInvariance.haltsOn_iso
---
The library's invariance theorem for the halting problem.
-/
theorem haltsOn_iso {A B : Type} [turing.Structure A] [turing.Structure B] (e : A ≃[turing] B) :
    HaltsOn A ↔ HaltsOn B :=
  DescriptiveComplexity.HALT.iso_invariant e

/--
---
conclusion: Lax624099.HaltingInvariance.halt_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem halt_iff (A : Type) [turing.Structure A] : HALT A ↔ HaltsOn A :=
  ofPred_iff @haltsOn_iso A

/-- The library's bundled HALT and the concept's agree on every instance. -/
theorem halt_agree (A : Type) [turing.Structure A] : DescriptiveComplexity.HALT A ↔ HALT A :=
  (halt_iff A).symm

/--
---
conclusion: Lax624099.CodeHaltingInvariance.codeHaltsOn_iso
---
The library's invariance theorem for code halting.
-/
theorem codeHaltsOn_iso {A B : Type} [code.Structure A] [code.Structure B] (e : A ≃[code] B) :
    CodeHaltsOn A ↔ CodeHaltsOn B :=
  DescriptiveComplexity.CODEHALT.iso_invariant e

/--
---
conclusion: Lax624099.CodeHaltingInvariance.codehalt_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem codehalt_iff (A : Type) [code.Structure A] : CODEHALT A ↔ CodeHaltsOn A :=
  ofPred_iff @codeHaltsOn_iso A

/-- The library's bundled CODEHALT and the concept's agree on every
instance. -/
theorem codehalt_agree (A : Type) [code.Structure A] :
    DescriptiveComplexity.CODEHALT A ↔ CODEHALT A :=
  (codehalt_iff A).symm

/--
---
conclusion: Lax624099.PostCorrespondenceInvariance.pcpOn_iso
---
The library's invariance theorem for Post's correspondence problem.
-/
theorem pcpOn_iso {A B : Type} [pcp.Structure A] [pcp.Structure B] (e : A ≃[pcp] B) :
    Pcp.PcpOn A ↔ Pcp.PcpOn B :=
  ⟨DescriptiveComplexity.Pcp.pcpOn_map e, DescriptiveComplexity.Pcp.pcpOn_map e.symm⟩

/--
---
conclusion: Lax624099.PostCorrespondenceInvariance.pcp_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem pcp_iff (A : Type) [pcp.Structure A] : PCP A ↔ Pcp.PcpOn A :=
  ofPred_iff @pcpOn_iso A

/-- The library's bundled PCP and the concept's agree on every instance. -/
theorem pcp_agree (A : Type) [pcp.Structure A] : DescriptiveComplexity.PCP A ↔ PCP A :=
  (pcp_iff A).symm

/-! ### The class -/

/--
---
conclusion: Lax624099.REClosure.RE_mem_of_foReduction
---
The library's closure of definability with value invention under
first-order reductions.
-/
theorem RE_mem_of_foReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : FOReduction P Q) (h : RE.Mem Q) :
    RE.Mem P :=
  DescriptiveComplexity.SigmaSONewDefinable.of_foReduction f h

/--
---
conclusion: Lax624099.REClosure.RE_mem_of_orderedReduction
---
The library's closure of definability with value invention under ordered
first-order reductions.
-/
theorem RE_mem_of_orderedReduction {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : OrderedFOReduction P Q) (h : RE.Mem Q) :
    RE.Mem P :=
  DescriptiveComplexity.SigmaSONewDefinable.of_orderedReduction f h

/--
---
conclusion: Lax624099.REFinite.RE_mem_congr_finite
---
Definability with value invention reads a problem on finite structures only.
-/
theorem RE_mem_congr_finite {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) : RE.Mem P ↔ RE.Mem Q :=
  DescriptiveComplexity.sigmaSONewDefinable_congr h

/--
---
conclusion: Lax624099.NPSubsetRE.NP_subset_RE
---
An existential second-order definition is one with value invention that
invents nothing.
-/
theorem NP_subset_RE {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L) (h : NP.Mem P) :
    RE.Mem P :=
  DescriptiveComplexity.SigmaSODefinable.toNew h

/-! ### Completeness -/

/--
---
conclusion: Lax624099.FinsatREComplete.finsat_RE_complete
---
Membership from the library's definition of finite satisfiability with value
invention; hardness from the library's generic reduction of any problem
definable with value invention to finite satisfiability. Both are transported
to the concept's problem along the agreement.
-/
theorem finsat_RE_complete : RE.Complete FINSAT :=
  ⟨(Lax624099.REFinite.RE_mem_congr_finite fun A _ _ => finsat_agree A).mp
      DescriptiveComplexity.finsat_mem_RE,
    Lax904597.NPClass.cofinalHard_congr (fun A _ _ => finsat_agree A)
      DescriptiveComplexity.FINSAT_RE_complete.2⟩

/--
---
conclusion: Lax624099.CodehaltREComplete.codehalt_RE_complete
---
Membership from the library's definition of code halting with value
invention; hardness because finite satisfiability, recursively enumerable on
concrete instances, reduces to code halting by the library's ordered
reduction, and is RE-hard by this submission's statement.
-/
theorem codehalt_RE_complete : RE.Complete CODEHALT :=
  ⟨(Lax624099.REFinite.RE_mem_congr_finite fun A _ _ => codehalt_agree A).mp
      DescriptiveComplexity.codehalt_mem_RE,
    (DescriptiveComplexity.orderedReduction_codehalt DescriptiveComplexity.FINSAT
      DescriptiveComplexity.finsat_rePred).elim fun f =>
      Lax904597.NPClass.cofinalHard_of_orderedReduction
        (OrderedFOReduction.congr finsat_agree codehalt_agree f)
        Lax624099.FinsatREComplete.finsat_RE_complete.2⟩

/--
---
conclusion: Lax624099.HaltREComplete.halt_RE_complete
---
Membership from the library's definition of unbounded acceptance with value
invention; hardness because finite satisfiability, recursively enumerable on
concrete instances, reduces to the halting problem by the library's ordered
reduction, the machine bridge, and is RE-hard by this submission's statement.
-/
theorem halt_RE_complete : RE.Complete HALT :=
  ⟨(Lax624099.REFinite.RE_mem_congr_finite fun A _ _ => halt_agree A).mp
      DescriptiveComplexity.halt_mem_RE,
    (DescriptiveComplexity.orderedReduction_halt DescriptiveComplexity.FINSAT
      DescriptiveComplexity.finsat_rePred).elim fun f =>
      Lax904597.NPClass.cofinalHard_of_orderedReduction
        (OrderedFOReduction.congr finsat_agree halt_agree f)
        Lax624099.FinsatREComplete.finsat_RE_complete.2⟩

/--
---
conclusion: Lax624099.PcpREComplete.pcp_RE_complete
---
Membership from the library's definition of matching with value invention;
hardness from the library's computation-history reduction of the halting
problem to Post's correspondence problem, the halting problem being RE-hard
by this submission's statement.
-/
theorem pcp_RE_complete : RE.Complete PCP :=
  ⟨(Lax624099.REFinite.RE_mem_congr_finite fun A _ _ => pcp_agree A).mp
      DescriptiveComplexity.pcp_mem_RE,
    Lax904597.NPClass.cofinalHard_of_orderedReduction
      (OrderedFOReduction.congr halt_agree pcp_agree
        DescriptiveComplexity.halt_ordered_fo_reduction_pcp)
      Lax624099.HaltREComplete.halt_RE_complete.2⟩

/-! ### Computability -/

/--
---
conclusion: Lax624099.REIsRecursivelyEnumerable.mem_RE_iff_rePred
---
The library's identification of definability with value invention and
recursive enumerability of the concrete instances, through code halting in
both directions.
-/
theorem mem_RE_iff_rePred {L : Language.{0, 0}} [L.IsRelational] (V : FinVocab L)
    (P : DecisionProblem L) : RE.Mem P ↔ REPred (DecisionProblem.toPred P V) :=
  DescriptiveComplexity.mem_RE_iff_rePred V P

/--
---
conclusion: Lax624099.ReductionsComputable.not_computablePred_of_relOrderedReduction
---
The library's computability of relativized ordered first-order reductions.
-/
theorem not_computablePred_of_relOrderedReduction {L L' : Language.{0, 0}} [L.IsRelational]
    [L'.IsRelational] {P : DecisionProblem L} {Q : DecisionProblem L'}
    (f : RelOrderedFOReduction P Q) (V : FinVocab L) (V' : FinVocab L')
    (hP : ¬ComputablePred (DecisionProblem.toPred P V)) :
    ¬ComputablePred (DecisionProblem.toPred Q V') :=
  DescriptiveComplexity.not_computablePred_of_relOrderedReduction f V V' hP

/--
---
conclusion: Lax624099.REHardUndecidable.not_computablePred_of_RE_hard
---
The library's theorem: code halting is undecidable since Mathlib's halting
problem is, and an RE-hard problem is reduced to by code halting.
-/
theorem not_computablePred_of_RE_hard {L : Language.{0, 0}} [L.IsRelational]
    {P : DecisionProblem L} (hP : RE.Hard P) (V : FinVocab L) :
    ¬ComputablePred (DecisionProblem.toPred P V) :=
  DescriptiveComplexity.not_computablePred_of_RE_hard hP V

/--
---
conclusion: Lax624099.Trakhtenbrot.finsat_not_computable
---
Finite satisfiability is RE-hard, and every RE-hard problem is undecidable.
-/
theorem finsat_not_computable : ¬ComputablePred (DecisionProblem.toPred FINSAT finsatVocab) :=
  Lax624099.REHardUndecidable.not_computablePred_of_RE_hard
    Lax624099.FinsatREComplete.finsat_RE_complete.2 finsatVocab

/--
---
conclusion: Lax624099.HaltingUndecidable.halt_not_computable
---
The halting problem is RE-hard, and every RE-hard problem is undecidable.
-/
theorem halt_not_computable (V : FinVocab turing) :
    ¬ComputablePred (DecisionProblem.toPred HALT V) :=
  Lax624099.REHardUndecidable.not_computablePred_of_RE_hard
    Lax624099.HaltREComplete.halt_RE_complete.2 V

/--
---
conclusion: Lax624099.HaltingUndecidable.codehalt_not_computable
---
Code halting is RE-hard, and every RE-hard problem is undecidable.
-/
theorem codehalt_not_computable : ¬ComputablePred (DecisionProblem.toPred CODEHALT codeVocab) :=
  Lax624099.REHardUndecidable.not_computablePred_of_RE_hard
    Lax624099.CodehaltREComplete.codehalt_RE_complete.2 codeVocab

/--
---
conclusion: Lax624099.PcpUndecidable.pcp_not_computable
---
Post's correspondence problem is RE-hard, and every RE-hard problem is
undecidable.
-/
theorem pcp_not_computable (V : FinVocab pcp) : ¬ComputablePred (DecisionProblem.toPred PCP V) :=
  Lax624099.REHardUndecidable.not_computablePred_of_RE_hard
    Lax624099.PcpREComplete.pcp_RE_complete.2 V

/--
---
conclusion: Lax624099.RENeCoRE.codehalt_not_mem_coRE
---
Were the complement of code halting recursively enumerable, code halting
would be decidable by Post's theorem, against the library's undecidability of
code halting; recursive enumerability on concrete instances is this
submission's statement.
-/
theorem codehalt_not_mem_coRE : ¬coRE.Mem CODEHALT := by
  intro h2
  have h1 : RE.Mem CODEHALT := Lax624099.CodehaltREComplete.codehalt_RE_complete.1
  refine DescriptiveComplexity.not_computablePred_codehalt ?_
  have e : DecisionProblem.toPred DescriptiveComplexity.CODEHALT codeVocab =
      DecisionProblem.toPred CODEHALT codeVocab :=
    funext fun s => propext (codehalt_agree _)
  rw [e]
  exact ComputablePred.computable_iff_re_compl_re'.mpr
    ⟨(Lax624099.REIsRecursivelyEnumerable.mem_RE_iff_rePred codeVocab CODEHALT).mp h1,
      (Lax624099.REIsRecursivelyEnumerable.mem_RE_iff_rePred codeVocab
        (DecisionProblem.compl CODEHALT)).mp h2⟩

/--
---
conclusion: Lax624099.RENeCoRE.RE_ne_coRE
---
Code halting is in RE and not in co-RE.
-/
theorem RE_ne_coRE : RE ≠ coRE :=
  fun h => Lax624099.RENeCoRE.codehalt_not_mem_coRE
    (h ▸ Lax624099.CodehaltREComplete.codehalt_RE_complete.1)

end Lax624099Proofs.Bridge
