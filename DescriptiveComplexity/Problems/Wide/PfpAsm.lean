/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Wide.PfpKit

/-!
# Assembling a program from call sites

The EXPSPACE program is large, but its rule set is a **sum over call sites**
of small, separately checkable contributions – kit instantiations plus their
exit rules. This file is the assembly: a
`DescriptiveComplexity.Pfp.Assembly` packages a family of per-site rule
shapes, an ownership map from phases to sites, and the two coherence facts
(every rule fires from a phase its site owns; each site separates in-shape);
`DescriptiveComplexity.Pfp.Assembly.prog` is the program whose rule names are
the sigma, and `DescriptiveComplexity.Pfp.Assembly.sep` its separation –
via `DescriptiveComplexity.Pfp.sep_sigma`, so
`DescriptiveComplexity.Pfp.Table.deterministic` applies with no global case
bash.

The point of the shape: the concrete program need never be stated as one
monolithic rule inductive. Each call site is built and checked in its own
file – its `Sh i` a kit rule type (or a sum of one with its exit rules), its
`hsep i` the kit's `sep` plus its `exit_disjoint` – and the assembly is the
only place they meet.
-/

namespace DescriptiveComplexity

namespace Pfp

open FirstOrder

open Language Structure

/-- **A program assembled from call sites**: a family of rule shapes, one per
site, an ownership map from phases to sites, and the two coherence facts that
make the whole separate. The remaining fields of
`DescriptiveComplexity.Pfp.Prog` – the designated elements and the machine's
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
the sites' own separation – `DescriptiveComplexity.Pfp.Prog.sep_of` then
yields `DescriptiveComplexity.Pfp.Table.Sep`, and with
`DescriptiveComplexity.Pfp.Table.deterministic` the emitted instance is
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

end Pfp

end DescriptiveComplexity
