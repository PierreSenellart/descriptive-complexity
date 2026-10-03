import Lax904597.CookLevin
import Lax904597.NPClass
import Lax799700.Hamilton
import Lax799700Proofs.Bridge.Common
import Lax799700Proofs.DescriptiveComplexity.Problems.Hamilton.Defs
import Lax799700Proofs.DescriptiveComplexity.Problems.Hamilton.Membership
import Lax799700Proofs.DescriptiveComplexity.Problems.Hamilton.Hardness
import Lax799700Proofs.Bridge.CliqueFamily
import Lax799700Proofs.DescriptiveComplexity.Problems.Hamilton.Reductions

namespace Lax799700Proofs.Bridge.Hamilton

open FirstOrder FirstOrder.Language
open Lax904597.Problems Lax904597.Interpretations Lax904597.Relativized Lax904597.Classes Lax799700.Problems Lax799700.Hamilton

/--
---
conclusion: Lax799700.Hamilton.hasHamCircuit_iso
---
The library's invariance theorem for HasHamCircuit.
-/
theorem hasHamCircuit_iso {A B : Type} [Lax799700.Hamilton.digraph.Structure A] [Lax799700.Hamilton.digraph.Structure B] (e : A ≃[Lax799700.Hamilton.digraph] B) :
    HasHamCircuit A ↔ HasHamCircuit B :=
  DescriptiveComplexity.hasHamCircuit_iso e

/--
---
conclusion: Lax799700.Hamilton.hamCircuit_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem hamCircuit_iff (A : Type) [Lax799700.Hamilton.digraph.Structure A] : HamCircuit A ↔ HasHamCircuit A :=
  Common.ofPred_iff @DescriptiveComplexity.hasHamCircuit_iso A

/-- The library's bundled HamCircuit and the catalog's agree on every structure. -/
theorem hamCircuit_agree (A : Type) [Lax799700.Hamilton.digraph.Structure A] : DescriptiveComplexity.HamCircuit A ↔ HamCircuit A :=
  (hamCircuit_iff A).symm

/--
---
conclusion: Lax799700.Hamilton.hamCircuit_NP_complete
---
Membership from the library's existential second-order definition of
HamCircuit; hardness from the library's reduction out of VertexCover, which is
NP-hard by the catalog’s statement for it. Both are transported to the
catalog's problems along the agreements.
-/
theorem hamCircuit_NP_complete : NP.Complete HamCircuit :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => hamCircuit_agree A).mp DescriptiveComplexity.hamCircuit_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_relOrderedReduction
      (Common.RelOrderedFOReduction.congr Lax799700Proofs.Bridge.CliqueFamily.vertexCover_agree hamCircuit_agree DescriptiveComplexity.vertexCover_rel_ordered_fo_reduction_hamCircuit) Lax799700.CliqueFamily.vertexCover_NP_complete.2⟩

/--
---
conclusion: Lax799700.Hamilton.hasDirHamCircuit_iso
---
The library's invariance theorem for HasDirHamCircuit.
-/
theorem hasDirHamCircuit_iso {A B : Type} [Lax799700.Hamilton.digraph.Structure A] [Lax799700.Hamilton.digraph.Structure B] (e : A ≃[Lax799700.Hamilton.digraph] B) :
    HasDirHamCircuit A ↔ HasDirHamCircuit B :=
  DescriptiveComplexity.hasDirHamCircuit_iso e

/--
---
conclusion: Lax799700.Hamilton.dirHamCircuit_iff
---
The problem given by an invariant property holds exactly where the property
does.
-/
theorem dirHamCircuit_iff (A : Type) [Lax799700.Hamilton.digraph.Structure A] : DirHamCircuit A ↔ HasDirHamCircuit A :=
  Common.ofPred_iff @DescriptiveComplexity.hasDirHamCircuit_iso A

/-- The library's bundled DirHamCircuit and the catalog's agree on every structure. -/
theorem dirHamCircuit_agree (A : Type) [Lax799700.Hamilton.digraph.Structure A] : DescriptiveComplexity.DirHamCircuit A ↔ DirHamCircuit A :=
  (dirHamCircuit_iff A).symm

/--
---
conclusion: Lax799700.Hamilton.dirHamCircuit_NP_complete
---
Membership from the library's existential second-order definition of
DirHamCircuit; hardness from the library's reduction out of HamCircuit, which
is NP-hard by the catalog’s statement for it. Both are transported to the
catalog's problems along the agreements.
-/
theorem dirHamCircuit_NP_complete : NP.Complete DirHamCircuit :=
  ⟨(Lax904597.NPClass.NP_mem_congr_finite fun A _ _ => dirHamCircuit_agree A).mp DescriptiveComplexity.dirHamCircuit_sigmaSODefinable,
    Lax904597.NPClass.cofinalHard_of_foReduction
      (Common.FOReduction.congr Lax799700Proofs.Bridge.Hamilton.hamCircuit_agree dirHamCircuit_agree DescriptiveComplexity.hamCircuit_fo_reduction_dirHamCircuit) Lax799700.Hamilton.hamCircuit_NP_complete.2⟩

end Lax799700Proofs.Bridge.Hamilton
