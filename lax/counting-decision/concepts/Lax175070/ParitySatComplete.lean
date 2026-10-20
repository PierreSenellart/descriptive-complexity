import Lax904597.Problems
import Lax485149.Problems
import Lax485149.Complement
import Lax904597.Classes
import Lax904597.Sat
import Lax904597.Interpretations
import Lax904597.Machines
import Lax564036.Hierarchy
import Lax366625.CountingProblems
import Lax366625.CountingClasses
import Lax366625.WitnessCounting
import Lax366625.CountingSat
import Lax366625.CountingRuns
import Lax175070.CountDefinability
import Lax175070.SelectedSat

/-!
---
title: ⊕SAT and Mod_k-SAT are complete
type: theorem
---
⊕SAT is ⊕P-complete and Mod$_k$-SAT is Mod$_k$P-complete. More generally,
the parity, and the residue modulo $k$, of every parsimoniously #P-complete
counting problem are complete for ⊕P and Mod$_k$P: a parsimonious reduction
preserves every property of the count. And a problem is in ⊕P, or in
Mod$_k$P, exactly when it reduces by an ordered first-order reduction to the
parity, or the residue, of the number of accepting runs of a
nondeterministic Turing machine.
-/

namespace Lax175070.ParitySatComplete

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Classes Lax904597.Sat Lax904597.Interpretations
    Lax904597.Machines Lax564036.Hierarchy
open Lax366625.CountingProblems Lax366625.CountingClasses Lax366625.WitnessCounting
    Lax366625.CountingSat
open Lax366625.CountingRuns Lax175070.CountDefinability Lax175070.SelectedSat Lax485149.Problems
open Lax485149.Complement

/-- ⊕SAT is ⊕P-complete. -/
axiom paritySat_parityP_complete :
  ParityP.Complete ParitySAT

/-- Mod_k-SAT is Mod_k P-complete. -/
axiom modSat_modP_complete :
  ∀ (k : ℕ), (ModP k).Complete (ModSAT k)

/-- The parity of a parsimoniously #P-complete problem is ⊕P-complete. -/
axiom parityP_complete_of_sharpP_parsimoniousComplete :
  ∀ {L : Language.{0, 0}} [L.IsRelational] {C : CountingProblem L},
    SharpP.ParsimoniousComplete C → ParityP.Complete (decide Odd C)

/-- The residue modulo `k` of a parsimoniously #P-complete problem is Mod_k P-complete. -/
axiom modP_complete_of_sharpP_parsimoniousComplete :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (k : ℕ) {C : CountingProblem L},
    SharpP.ParsimoniousComplete C → (ModP k).Complete (decide (fun c => ¬ k ∣ c) C)

/-- ⊕P is reducibility to the parity of the number of accepting runs. -/
axiom mem_parityP_iff_le_parity_sharpNtmAccept :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
    ParityP.Mem P ↔ Nonempty (OrderedFOReduction P (decide Odd SharpNTMAccept))

/-- Mod_k P is reducibility to the residue of the number of accepting runs. -/
axiom mem_modP_iff_le_mod_sharpNtmAccept :
  ∀ {L : Language.{0, 0}} [L.IsRelational] (k : ℕ) (P : DecisionProblem L),
    (ModP k).Mem P ↔ Nonempty (OrderedFOReduction P (decide (fun c => ¬ k ∣ c) SharpNTMAccept))

end Lax175070.ParitySatComplete
