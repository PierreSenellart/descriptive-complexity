/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpProg
import DescriptiveComplexity.Problems.Machine.DetRun

/-!
# The accepting phase is a dead end

The side condition every discharge of a *no*-instance in
`DescriptiveComplexity.Problems.Machine.DetRun` asks for, at the EXPSPACE
program: **accepting configurations are stuck**. With it,
`DescriptiveComplexity.TMData.not_acceptsSpace_of_reaches_dead` (a run that
ends badly) and `DescriptiveComplexity.TMData.not_acceptsSpace_of_chain` (a run
that never ends) are the two ways the reduction rejects, and no invariant over
the program's rules is needed for either.

`DescriptiveComplexity.Pfp.Assembly` already carries the fact, in its
`owner`/`howner` fields: every rule fires from a phase its own site owns, so a
phase whose owning site contributes *no* rules is the source of none
(`DescriptiveComplexity.Pfp.Assembly.srcPh_ne_of_isEmpty`). The accepting
phase is such a phase – `OuterSh … .accept` is `Empty` – whence
`DescriptiveComplexity.Pfp.PfpData.srcPh_ne_acceptP` and, at the machine,
`DescriptiveComplexity.Pfp.PfpData.stuck_acc`. That is what makes a false
output a *rejection* rather than a detour, and it costs one case analysis on
the tag of a transition rather than one per rule.
-/

namespace DescriptiveComplexity

namespace Pfp

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

namespace PfpData

variable {L : Language.{0, 0}} {dt : PfpData L} {A Q : Type} {zero one : A}
variable [LinearOrder A] [Fintype Q] [Fintype dt.SlotIx]
variable {hzo : zero ≠ one}
variable {args : ∀ v : dt.VarIx, dt.VarArgs (A := A) (Q := Q) v}
variable [LinearOrder (dt.RIx zero one hzo args)] [LinearOrder dt.PF]
variable {hpl : Fintype.card (Q ⊕ dt.SlotIx) ≤ dt.dd}
variable [LinearOrder dt.KIx]
variable [Language.wide.Structure (Univ A (dt.RIx zero one hzo args) dt.PF
  dt.KIx dt.dd)]

omit [LinearOrder dt.KIx]
  [Language.wide.Structure (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
    dt.dd)] in
/-- **No rule of the program leaves the accepting phase**: its site
(`DescriptiveComplexity.Pfp.OuterSite.accept`) contributes none. -/
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
    {e : Config (WPoint (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
      dt.dd))}
    (hst : e.state = Sum.inr (PfpTag.phase p, w)) (e' : Config (WPoint (Univ A
      (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd))) :
    ¬(wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      e e' := by
  rintro ⟨τ, htr, hsrc, -⟩
  rw [hst] at hsrc
  match τ with
  | Sum.inl _ => exact htr
  | Sum.inr (t, v) =>
    have htr' : WMTr ((t, v) : Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
      dt.dd) := htr
    rw [hR.tr] at htr'
    have hsrc' : WMSrc ((t, v) : Univ A (dt.RIx zero one hzo args) dt.PF
      dt.KIx dt.dd) (PfpTag.phase p, w) := hsrc
    rw [hR.src] at hsrc'
    match t with
    | .ctrl r =>
      have htag : (PfpTag.phase p : PfpTag (dt.RIx zero one hzo args) dt.PF
          dt.KIx) =
          PfpTag.phase ((dt.prog zero one hzo args hpl).rules r).srcPh :=
        congrArg Prod.fst hsrc'
      exact hp r (PfpTag.phase.inj htag).symm
    | .sym => exact htr'
    | .phase _ => exact htr'
    | .arg _ => exact htr'

/-- **Accepting configurations of the emitted machine are stuck** – the `hsink`
side condition of `DescriptiveComplexity.Problems.Machine.DetRun`. An accepting
state is a `phase`-tagged element whose phase the program accepts, and the
program accepts only `acceptP`. -/
theorem stuck_acc (hR : (dt.prog zero one hzo args hpl).table.Reads)
    (e : Config (WPoint (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
      dt.dd)))
    (hacc : (wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
      dt.dd)).Acc e.state)
    (e' : Config (WPoint (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx
      dt.dd))) :
    ¬(wideData (Univ A (dt.RIx zero one hzo args) dt.PF dt.KIx dt.dd)).Step
      e e' := by
  match hs : e.state with
  | Sum.inl _ => rw [hs] at hacc; exact hacc.elim
  | Sum.inr (t, v) =>
    rw [hs] at hacc
    have hacc' : WMAcc ((t, v) : Univ A (dt.RIx zero one hzo args) dt.PF
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

end PfpData

end Pfp

end DescriptiveComplexity
