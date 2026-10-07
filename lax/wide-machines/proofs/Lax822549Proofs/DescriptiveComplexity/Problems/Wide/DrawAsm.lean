/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax822549Proofs.DescriptiveComplexity.Problems.Wide.DrawKit
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

/-!
# Assembling a program from call sites

The EXPSPACE program is large, but its rule set is a **sum over call sites**
of small, separately checkable contributions – kit instantiations plus their
exit rules. This file is the assembly: a
`DescriptiveComplexity.Draw.Assembly` packages a family of per-site rule
shapes, an ownership map from phases to sites, and the two coherence facts
(every rule fires from a phase its site owns; each site separates in-shape);
`DescriptiveComplexity.Draw.Assembly.prog` is the program whose rule names are
the sigma, and `DescriptiveComplexity.Draw.Assembly.sep` its separation –
via `DescriptiveComplexity.Draw.sep_sigma`, so
`DescriptiveComplexity.Draw.Table.deterministic` applies with no global case
bash.

The point of the shape: the concrete program need never be stated as one
monolithic rule inductive. Each call site is built and checked in its own
file – its `Sh i` a kit rule type (or a sum of one with its exit rules), its
`hsep i` the kit's `sep` plus its `exit_disjoint` – and the assembly is the
only place they meet.
-/

namespace Lax822549Proofs.DescriptiveComplexity

namespace Draw

open FirstOrder

open Language Structure

/-- **A program assembled from call sites**: a family of rule shapes, one per
site, an ownership map from phases to sites, and the two coherence facts that
make the whole separate. The remaining fields of
`DescriptiveComplexity.Draw.Prog` – the designated elements and the machine's
constants – are carried alongside, untouched by the assembly. -/
structure Assembly (A Q W P S : Type) [Fintype Q] [Fintype W] where
  /-- The rule shape of each site. -/
  Sh : S → Type
  /-- The rules each site contributes. -/
  rule : ∀ i : S, Sh i → Rule A Q W P
  /-- Which site owns each phase. -/
  owner : P → S
  /-- Every rule fires from a phase its site owns. -/
  howner : ∀ (i : S) (ρ : Sh i), owner (rule i ρ).srcPh = i
  /-- Each site separates in-shape. -/
  hsep : ∀ (i : S) (ρ ρ' : Sh i) (f : Q → A) (g : W → A),
    (rule i ρ).guard f g → (rule i ρ').guard f g →
    (rule i ρ).srcPh = (rule i ρ').srcPh → ρ = ρ'

namespace Assembly

variable {A Q W P S K : Type} {dd : ℕ} [Fintype Q] [Fintype W]

variable (asm : Assembly A Q W P S)

/-- **The assembled program**: rule names are the sigma of the sites' shapes;
everything else is the supplied constants. -/
def prog (zero one : A) (hzo : zero ≠ one)
    (hpl : Fintype.card (Q ⊕ W) ≤ dd) (startPh : P) (startSt : Q → A)
    (accept : P → (Q → A) → Prop) (blank : W → A)
    (mark : Univ A ((i : S) × asm.Sh i) P K dd → W → A) :
    Prog A ((i : S) × asm.Sh i) P Q W K dd where
  zero := zero
  one := one
  zero_ne_one := hzo
  payload_le := hpl
  rules := fun r => asm.rule r.1 r.2
  startPh := startPh
  startSt := startSt
  accept := accept
  blank := blank
  mark := mark

/-- **The assembled program separates**: cross-site by ownership, in-site by
the sites' own separation – `DescriptiveComplexity.Draw.Prog.sep_of` then
yields `DescriptiveComplexity.Draw.Table.Sep`, and with
`DescriptiveComplexity.Draw.Table.deterministic` the emitted instance is
deterministic. -/
theorem sep {zero one : A} {hzo : zero ≠ one} {hpl : Fintype.card (Q ⊕ W) ≤ dd}
    {startPh : P} {startSt : Q → A} {accept : P → (Q → A) → Prop}
    {blank : W → A} {mark : Univ A ((i : S) × asm.Sh i) P K dd → W → A} :
    (asm.prog (K := K) (dd := dd) zero one hzo hpl startPh startSt accept
      blank mark).table.Sep :=
  Prog.sep_of _
    (sep_sigma (fun r => asm.rule r.1 r.2) asm.owner
      (fun i ρ => asm.howner i ρ) (fun i ρ ρ' f g => asm.hsep i ρ ρ' f g))

end Assembly

end Draw

end Lax822549Proofs.DescriptiveComplexity


