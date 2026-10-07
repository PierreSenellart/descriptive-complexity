/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawProg
import Lax822549Proofs.DescriptiveComplexity.Problems.Machine.DetRun
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
import Lax822549.WideMachines
import Lax822549.WideRegChannel
import Lax822549.WideTilings
import Lax904597.Classes
import Lax904597.Interpretations
import Lax904597.Machines
import Lax904597.Problems
import Lax904597.Relativized
import Lax904597.Sat
import Lax904597.SecondOrder

namespace Lax822549.WideMachines
end Lax822549.WideMachines

namespace Lax904597.Machines
end Lax904597.Machines

namespace FirstOrder.Language
export Lax822549.WideMachines (wide)
end FirstOrder.Language

namespace Lax822549Proofs.DescriptiveComplexity
export Lax822549.WideMachines (WMAcc WMSrc WMTr WPoint wideData)
end Lax822549Proofs.DescriptiveComplexity

namespace Lax822549Proofs.DescriptiveComplexity
export Lax904597.Machines (Config)
end Lax822549Proofs.DescriptiveComplexity

/-!
# The accepting phase is a dead end

The side condition every discharge of a *no*-instance in
`DescriptiveComplexity.Problems.Machine.DetRun` asks for, at the EXPSPACE
program: **accepting configurations are stuck**. With it,
`DescriptiveComplexity.TMData.not_acceptsSpace_of_reaches_dead` (a run that
ends badly) and `DescriptiveComplexity.TMData.not_acceptsSpace_of_chain` (a run
that never ends) are the two ways the reduction rejects, and no invariant over
the program's rules is needed for either.

`DescriptiveComplexity.Draw.Assembly` already carries the fact, in its
`owner`/`howner` fields: every rule fires from a phase its own site owns, so a
phase whose owning site contributes *no* rules is the source of none
(`DescriptiveComplexity.Draw.Assembly.srcPh_ne_of_isEmpty`). The accepting
phase is such a phase – `OuterSh … .accept` is `Empty` – whence
`DescriptiveComplexity.Draw.Data.srcPh_ne_acceptP` and, at the machine,
`DescriptiveComplexity.Draw.Data.stuck_acc`. That is what makes a false
output a *rejection* rather than a detour, and it costs one case analysis on
the tag of a transition rather than one per rule.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-! ### A phase whose site has no rules -/

namespace Assembly

variable {A Q W P S : Type} [Fintype Q] [Fintype W]

/-- **A phase owned by a site with no rules is the source of no rule.** Every
rule fires from a phase its own site owns (`Assembly.howner`), so a rule with
that source phase would be a rule of that site – and there are none. -/
theorem srcPh_ne_of_isEmpty (asm : Assembly A Q W P S) {p : P}
    (hp : IsEmpty (asm.Sh (asm.owner p))) (i : S) (ρ : asm.Sh i) :
    (asm.rule i ρ).srcPh ≠ p := by
  intro h
  have hi : asm.owner p = i := h ▸ asm.howner i ρ
  exact hp.elim (cast (congrArg asm.Sh hi.symm) ρ)

end Assembly

/-! ### The emitted machine is stuck in its accepting phase -/

namespace Data

variable {L : Language.{0, 0}} {dt : Data L} {A Q : Type} {zero one : A}

variable [LinearOrder A] [Fintype Q] [Fintype dt.SlotIx]

variable {hzo : zero ≠ one}

variable {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v}

variable [LinearOrder (dt.RIx zero one hzo args)] [LinearOrder dt.PF]

variable {hpl : Fintype.card (Q ⊕ dt.SlotIx) ≤ dt.dd}

variable [LinearOrder dt.KIx]

variable [Lax822549.WideMachines.wide.Structure (Univ A (dt.RIx zero one hzo args) dt.PF
  dt.KIx dt.dd)]

omit [LinearOrder dt.KIx]
  [Lax822549.WideMachines.wide.Structure (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
    dt.dd)] in
/-- **No rule of the program leaves the accepting phase**: its site
(`DescriptiveComplexity.Draw.OuterSite.accept`) contributes none. -/
theorem srcPh_ne_acceptP (r : dt.RIx zero one hzo args) :
    ((dt.prog zero one hzo args hpl).rules r).srcPh ≠ OuterPh.acceptP :=
  (dt.progAsm zero one hzo args).srcPh_ne_of_isEmpty
    (p := OuterPh.acceptP) ⟨fun e => nomatch e⟩ r.1 r.2

/-- **A configuration in a phase no rule leaves is stuck.** A step needs a
transition whose source state is the machine's, and a transition's source state
carries the source phase of its rule in its *tag* – so the case analysis is on
the tag, not on the rules. -/
theorem stuck_of_srcPh_ne
    (hR : (dt.prog zero one hzo args hpl).table.Reads) {p : dt.PF}
    (hp : ∀ r : dt.RIx zero one hzo args,
      ((dt.prog zero one hzo args hpl).rules r).srcPh ≠ p)
    {w : Fin dt.dd → A}
    {e : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
      dt.dd))}
    (hst : e.state = Sum.inr (Tag.phase p, w)) (e' : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint (Univ A
      (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd))) :
    ¬(Lax822549.WideMachines.wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      e e' := by
  rintro ⟨τ, htr, hsrc, -⟩
  rw [hst] at hsrc
  match τ with
  | Sum.inl _ => exact htr
  | Sum.inr (t, v) =>
    have htr' : Lax822549.WideMachines.WMTr ((t, v) : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
      dt.dd) := htr
    rw [hR.tr] at htr'
    have hsrc' : Lax822549.WideMachines.WMSrc ((t, v) : Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd) (Tag.phase p, w) := hsrc
    rw [hR.src] at hsrc'
    match t with
    | .ctrl r =>
      have htag : (Tag.phase p : Tag (dt.RIx zero one hzo args) dt.PF
          dt.KIx) =
          Tag.phase ((dt.prog zero one hzo args hpl).rules r).srcPh :=
        congrArg Prod.fst hsrc'
      exact hp r (Tag.phase.inj htag).symm
    | .sym => exact htr'
    | .phase _ => exact htr'
    | .arg _ => exact htr'

/-- **Accepting configurations of the emitted machine are stuck** – the `hsink`
side condition of `DescriptiveComplexity.Problems.Machine.DetRun`. An accepting
state is a `phase`-tagged element whose phase the program accepts, and the
program accepts only `acceptP`. -/
theorem stuck_acc (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (e : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
      dt.dd)))
    (hacc : (Lax822549.WideMachines.wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
      dt.dd)).Acc e.state)
    (e' : Lax904597.Machines.Config (Lax822549.WideMachines.WPoint (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
      dt.dd))) :
    ¬(Lax822549.WideMachines.wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      e e' := by
  match hs : e.state with
  | Sum.inl _ => rw [hs] at hacc; exact hacc.elim
  | Sum.inr (t, v) =>
    rw [hs] at hacc
    have hacc' : Lax822549.WideMachines.WMAcc ((t, v) : Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd) := hacc
    rw [hR.acc] at hacc'
    match t with
    | .phase p =>
      obtain ⟨-, hp⟩ := hacc'
      exact stuck_of_srcPh_ne hR
        (hp.1 ▸ srcPh_ne_acceptP (hpl := hpl)) hs e'
    | .ctrl _ => exact hacc'.elim
    | .sym => exact hacc'.elim
    | .arg _ => exact hacc'.elim

end Data

end Draw

end Lax822549Proofs.DescriptiveComplexity


