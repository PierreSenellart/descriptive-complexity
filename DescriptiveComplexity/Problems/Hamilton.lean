/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.Hamilton.Defs
import DescriptiveComplexity.Problems.Hamilton.Cycle
import DescriptiveComplexity.Problems.Hamilton.Membership
import DescriptiveComplexity.Problems.Hamilton.Reductions
import DescriptiveComplexity.Problems.Hamilton.Hardness
import DescriptiveComplexity.Problems.CliqueFamily
import DescriptiveComplexity.Hierarchy

/-!
# Hamilton circuits are NP-complete

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
hardness only has to be proved on the undirected side. There it is Karp's
twelve-vertex cover-testing gadget, as the relativized ordered reduction
`DescriptiveComplexity.vertexCover_rel_ordered_fo_reduction_hamCircuit` from Vertex
Cover (`DescriptiveComplexity.Problems.Hamilton.Gadget` for the interpretation,
`Forward` and `Reverse` for the two directions of correctness, `Hardness` for
the assembly). Both problems are NP-complete – the last of Karp's 21.
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

/-- Hamilton Circuit is NP-hard: Vertex Cover, which is NP-hard, relativized-
ordered-FO-reduces to it by the cover-testing gadget interpretation
`DescriptiveComplexity.hamInterp`. -/
theorem hamCircuit_NP_hard : NP.Hard HamCircuit :=
  NP.hard_of_relOrderedReduction vertexCover_rel_ordered_fo_reduction_hamCircuit vertexCover_NP_hard

/-- Directed Hamilton Circuit is NP-hard: the undirected problem, now NP-hard,
FO-reduces to it by doubling each edge. -/
theorem dirHamCircuit_NP_hard : NP.Hard DirHamCircuit :=
  NP.hard_of_foReduction hamCircuit_fo_reduction_dirHamCircuit hamCircuit_NP_hard

/-- **Hamilton Circuit is NP-complete**, derived from the first-order
reductions of this library and the Cook–Levin theorem. -/
theorem hamCircuit_NP_complete : NP.Complete HamCircuit :=
  ⟨hamCircuit_mem_NP, hamCircuit_NP_hard⟩

/-- **Directed Hamilton Circuit is NP-complete** – closing Karp's 21. -/
theorem dirHamCircuit_NP_complete : NP.Complete DirHamCircuit :=
  ⟨dirHamCircuit_mem_NP, dirHamCircuit_NP_hard⟩

end DescriptiveComplexity
