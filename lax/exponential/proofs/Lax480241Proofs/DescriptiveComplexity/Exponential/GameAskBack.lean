/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax480241Proofs.DescriptiveComplexity.Exponential.GameAsk
import Lax480241Proofs.DescriptiveComplexity.Exponential.GameBack
import Lax134656.OrderFreeTransitiveClosure
import Lax134656.PartialFixedPoint
import Lax134656.Qsat
import Lax134656.SecondOrderTransitiveClosure
import Lax134656.SpaceBoundedMachines
import Lax134656.SuccinctReach
import Lax480241.AlternatingSpace
import Lax480241.Expansions
import Lax480241.SecondOrderFixedPoints
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
import Lax564036.AlternatingMachines
import Lax564036.Difference
import Lax564036.QuantifiedBooleanFormulas
import Lax564036.SatUnsat
import Lax564036.Tautology
import Lax564036.ThreeDnfTautology
import Lax799700.CliqueFamily
import Lax799700.Coloring
import Lax799700.Common
import Lax799700.DominatingSet
import Lax799700.Feedback
import Lax799700.Hamilton
import Lax799700.JobSequencing
import Lax799700.Knapsack
import Lax799700.MaxCut
import Lax799700.NaeSat
import Lax799700.NaeThreeSat
import Lax799700.OneInSat
import Lax799700.Partition
import Lax799700.SetFamily
import Lax799700.Steiner
import Lax799700.SubgraphIso
import Lax799700.ThreeColorability
import Lax799700.ThreeDimMatching
import Lax799700.ThreeSat
import Lax799700.ZeroOneIP
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax134656.SecondOrderTransitiveClosure.SOBlock
end Lax134656.SecondOrderTransitiveClosure.SOBlock

namespace Lax480241.AlternatingSpace.ATMData
end Lax480241.AlternatingSpace.ATMData

namespace Lax904597.Machines
end Lax904597.Machines

namespace Lax904597.SecondOrder
end Lax904597.SecondOrder

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.SecondOrder (SOBlock)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax480241Proofs.DescriptiveComplexity
export Lax904597.Machines (Config)
end Lax480241Proofs.DescriptiveComplexity

namespace Lax904597.SecondOrder.SOBlock
export Lax134656.SecondOrderTransitiveClosure.SOBlock (structure₂)
end Lax904597.SecondOrder.SOBlock

namespace Lax564036.AlternatingMachines.ATMData
export Lax480241.AlternatingSpace.ATMData (AltWin)
end Lax564036.AlternatingMachines.ATMData

/-!
# A question, read back

The mirror of `DescriptiveComplexity.GameProg.altWin_ask`: if the machine wins
from the entry of a question's prefix, the question holds.

## What the bridge has to say, backwards

* **an arrival is a correct claim.** `DescriptiveComplexity.SeekArrives` gives a
  cell whose symbol answered the test; unfolding
  `DescriptiveComplexity.GameProg.isTarget` says the symbol's bit *is* the claim,
  its region is the one the atom's copy names, and its address is the atom's
  arguments at the valuation. Since the tape's cell carries the bit the
  assignment gives it, the claim is right – and the region bookkeeping is
  `DescriptiveComplexity.GameProg.cond_copy` again, read the other way;
* **the seek's test never fires on a mark**, which the parametric layer had to
  assume and the program discharges by unfolding one existential;
* the tuple `SeekArrives` carries is *not* the one the forward direction builds,
  so the address it names has to be recovered from `argsOf` and the agreement
  with the phase's valuation – which is the only place the two halves of a
  transition's tuple are pulled apart backwards.
-/

namespace Lax480241Proofs.DescriptiveComplexity

open FirstOrder

open Language

namespace GameProg

variable {K : Language.{0, 0}} {B : Lax904597.SecondOrder.SOBlock} {V M : ℕ} (prog : GameProg K B V M)
  {A : Type} [K.Structure A] [LinearOrder A] [Finite A]
  {a₀ : A} {hdim : blockArityBound B ≤ gameDim B V} {ρ σ : B.Assignment A}

local notation "𝕄" => gameMachine prog.vars prog.pol a₀ hdim
  (gameRule prog.vars prog.natoms prog.concOk prog.isTarget)

variable {prog}

omit [K.Structure A] [LinearOrder A] [Finite A] in
/-- **The seek's test never fires on a mark**: it asks for the symbol of a cell,
which a sentinel's mark is not. -/
theorem not_isTarget_mark (p : MachPh V M) (b : Bool) (w : Fin (gameDim B V) → A) :
    ¬ prog.isTarget p (SymTag.mark b) w := by
  rintro ⟨h, hs, -⟩
  exact absurd hs (by simp)

omit [LinearOrder A] [Finite A] in
/-- **The guard of a concluding transition reads only the valuation the phase
declares.** -/
theorem concOk_congr {p : MachPh V M} {w vv : Fin (gameDim B V) → A}
    (hp : p.kind = .conc) (hag : Agree (MachPh.arity prog.vars p) w vv)
    (h : prog.concOk p w) : prog.concOk p vv := by
  have hac : MachPh.arity prog.vars p = prog.vars p.q :=
    MachPh.arity_of_matrix prog.vars (Or.inr (Or.inr (Or.inr hp)))
  have hval : prog.valOf p.q w = prog.valOf p.q vv := by
    funext l
    exact (hag _ (by rw [hac]; exact l.isLt)).symm
  rw [GameProg.concOk, ← hval]
  exact h

omit [K.Structure A] [Finite A] in
/-- **An arrival is a correct claim.** The cell the seek stopped at holds the
atom the challenge named, its bit is the one that was claimed, and the tape
gives that bit by the assignment of the region the atom's copy points to. -/
theorem holds_of_seekArrives (q : GameQuestion) (r par : Bool)
    {b : Fin M → Bool} {vv : Fin (gameDim B V) → A} {k : Fin (M + 1)}
    (hk : (k : ℕ) < (prog.data q).natoms) {pos : GamePt B V M A}
    (harr : SeekArrives a₀ prog.isTarget prog.vars (MachPh.seekPh q r b k par) vv
      (tapeOfAssign a₀ hdim ρ σ) pos) :
    b (Fin.castLE (prog.natoms_le q) ⟨(k : ℕ), hk⟩) = true ↔
      ((prog.data q).atoms ⟨(k : ℕ), hk⟩).Holds (cond r σ ρ) (cond (!r) σ ρ)
        (prog.valOf q vv) := by
  classical
  obtain ⟨bit, rr, i, ā, w, hposc, hsym, hag, hargs, htgt⟩ := harr
  obtain ⟨hk', hsymeq, hadr⟩ := htgt
  -- the atom the challenge names
  obtain ⟨hbit, hrr, hi⟩ : bit = b (Fin.castLE (prog.natoms_le q) ⟨(k : ℕ), hk⟩) ∧
      rr = (if ((prog.data q).atoms ⟨(k : ℕ), hk⟩).copy then !r else r) ∧
      i = ((prog.data q).atoms ⟨(k : ℕ), hk⟩).var := by
    have hs := hsymeq
    simp only [MachPh.seekPh, SymTag.val.injEq] at hs
    exact hs
  subst hi
  have hadr' : argsOf ((prog.data q).atoms ⟨(k : ℕ), hk⟩).var (addrOf w) =
      fun l => w (Fin.castLE (prog.vars_le_gameDim q)
        (((prog.data q).atoms ⟨(k : ℕ), hk⟩).args l)) := by
    have hd := hadr
    simp only [MachPh.seekPh] at hd
    exact hd
  -- its address is its arguments, read at the phase's valuation
  have hval : ā = fun l => prog.valOf q vv (((prog.data q).atoms ⟨(k : ℕ), hk⟩).args l) := by
    rw [← hargs, hadr']
    funext l
    exact (hag _ (((prog.data q).atoms ⟨(k : ℕ), hk⟩).args l).isLt).symm
  -- the tape gives the cell the bit its region's assignment does
  have htape : bit = decide (cond rr σ ρ ((prog.data q).atoms ⟨(k : ℕ), hk⟩).var ā) := by
    rw [hposc, tapeOfAssign_cellPt] at hsym
    exact (valPt_inj_bit a₀ hsym).symm
  rw [← hbit, htape, decide_eq_true_iff, BlockAtom.Holds, hrr, ← cond_copy, hval]

omit [Finite A] in
/-- **The matrix holds, read back from a winning claim phase**: the vector the
existential player claimed is correct at every atom the universal player could
have challenged, and the residue it leaves holds. -/
theorem matrixHolds_of_altWin (h₀ : IsBot a₀) {q : GameQuestion} {r par : Bool}
    {vv : Fin (gameDim B V) → A} {c : Lax904597.Machines.Config (GamePt B V M A)}
    (h : CtrlCfg a₀ hdim prog.vars ρ σ (MachPh.claimPh q r par) vv c)
    (hw : (𝕄).AltWin true c) :
    (prog.data q).MatrixHolds (cond r σ ρ) (cond (!r) σ ρ) (prog.valOf q vv) := by
  obtain ⟨b, harr, hconc⟩ :=
    claim_of_altWin (natoms := prog.natoms) (pol := prog.pol) h₀ rfl
      (fun _ _ _ _ => not_isTarget_mark _ _ _)
      (fun _ w hag hc => concOk_congr rfl hag hc) h hw
  refine ⟨fun j => b (Fin.castLE (prog.natoms_le q) j), fun j => ?_, hconc⟩
  obtain ⟨pos, -, harr'⟩ := harr ⟨(j : ℕ), by have := j.isLt; have := prog.natoms_le q; omega⟩
    j.isLt
  exact holds_of_seekArrives q r par j.isLt harr'

omit [Finite A] in
/-- **A question holds, read back**: if the machine wins from the entry of a
question's prefix, the question's sentence is true of the two assignments the
tape carries. This is the converse of
`DescriptiveComplexity.GameProg.altWin_ask`. -/
theorem ask_of_altWin (h₀ : IsBot a₀) (q : GameQuestion)
    {φ : ((K.sum B.lang).sum B.lang).Sentence} (hplays : (prog.data q).Plays φ)
    {r par : Bool} {jj : Fin (V + 1)} (hjj : (jj : ℕ) = 0)
    {vv : Fin (gameDim B V) → A} {c : Lax904597.Machines.Config (GamePt B V M A)}
    (h : CtrlCfg a₀ hdim prog.vars ρ σ (MachPh.prePh q r jj par) vv c)
    (hw : (𝕄).AltWin true c) :
    @Sentence.Realize _ A (B.structure₂ (cond r σ ρ) (cond (!r) σ ρ)) φ := by
  let : Nonempty A := ⟨a₀⟩
  refine (hplays A (cond r σ ρ) (cond (!r) σ ρ) (qval prog.vars_le q vv)).mpr ?_
  exact pre_of_altWin (natoms := prog.natoms) h₀ prog.vars_le
    (fun _ vv' c' h' hw' => matrixHolds_of_altWin h₀ h' hw')
    (prog.vars q) 0 (le_of_eq (Nat.sub_zero _)) (Nat.zero_le _) par jj hjj vv c h hw

end GameProg

end Lax480241Proofs.DescriptiveComplexity


