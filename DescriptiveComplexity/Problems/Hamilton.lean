/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Hamilton.Defs
import DescriptiveComplexity.Problems.Hamilton.Cycle
import DescriptiveComplexity.Problems.Hamilton.Membership
import DescriptiveComplexity.Problems.Hamilton.Reductions
import DescriptiveComplexity.Hierarchy

/-!
# Hamilton circuits

Umbrella file for Karp's DIRECTED HAMILTON CIRCUIT
(`DescriptiveComplexity.DirHamCircuit`) and HAMILTON CIRCUIT
(`DescriptiveComplexity.HamCircuit`), both on the vocabulary
`FirstOrder.Language.digraph` – a single binary relation, read as it stands by
the first problem and symmetrically by the second.

A circuit visiting every vertex exactly once is a **linear order of the
universe** whose consecutive elements are adjacent and whose last element is
adjacent to its first (`DescriptiveComplexity.TourOn`). That reading is what puts
both problems in NP without any path machinery
(`DescriptiveComplexity.dirHamCircuit_mem_NP`,
`DescriptiveComplexity.hamCircuit_mem_NP`): a linear order is a relation, so an
existential second-order block can guess it, and the four order axioms, “is
the immediate successor” and the two adjacency demands are first-order. It is
the device the job-sequencing certificate uses for its schedule, closed into a
cycle, and `DescriptiveComplexity.tourOn_iff_enum` checks that it is the intended
reading: a tour is exactly a cyclic enumeration of the universe along which
consecutive elements are adjacent.

The undirected problem reduces to the directed one by replacing each edge with
its two arcs (`DescriptiveComplexity.hamCircuit_fo_reduction_dirHamCircuit`), so
hardness only has to be proved on the undirected side; that gadget – Karp's,
from Vertex Cover – is not formalized yet (see `ROADMAP.md`).
-/

namespace DescriptiveComplexity

open FirstOrder

/-- Directed Hamilton Circuit is in NP: it is `Σ₁`-definable, the certificate
being the circuit, guessed as a linear order of the universe. -/
theorem dirHamCircuit_mem_NP : DirHamCircuit ∈ NP :=
  dirHamCircuit_sigmaSODefinable

/-- Hamilton Circuit is in NP, by the same certificate read on the
symmetrized arc relation. -/
theorem hamCircuit_mem_NP : HamCircuit ∈ NP :=
  hamCircuit_sigmaSODefinable

end DescriptiveComplexity
