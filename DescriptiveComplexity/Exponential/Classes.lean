/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.SecondOrderFixedPoint

/-!
# The exponential classes: EXPTIME, NEXPTIME, EXPSPACE

The three classes, and the bridge theorems that let everything else about them
be inherited rather than reproved.

| | definition | equal, by theorem |
|---|---|---|
| `DescriptiveComplexity.EXPTIME` | SO(≤, LFP) | `PTIME.exp` |
| `DescriptiveComplexity.NEXPTIME` | `NP.exp` – ∃SO over the expanded universe | – |
| `DescriptiveComplexity.EXPSPACE` | SO(≤, PFP) | `PSPACE.exp` |

The library elsewhere splits definition from theorem the other way round –
`PTIME` is *defined* by SO-Horn and equals FO(LFP) by theorem, `PSPACE` is
*defined* by SO(TC) and equals FO(PFP) by theorem. At the exponential level the
fixpoint logic takes the definition slot, because there is no comparably
canonical restricted syntax to define these classes by, and because naming a
class after its fixpoint is what makes its statements readable: `EXPTIME ⊆
EXPSPACE` is SO(LFP) ⊆ SO(PFP).

## Why NEXPTIME is presented differently

Its literature spelling is existential *third*-order logic ([Leivant
1989][leivant1989descriptive]; [Hella–Turull-Torres
2006][hella2006higher]), and this development deliberately builds no
third-order syntax layer: the two fixpoint logics need none, since an expansion
has already lowered the type of the objects a second-order fixpoint ranges
over. A "Σ¹₁ over the expansion" definition would be no more informative than
`NP.exp`, since that is what `NP.exp` unfolds to. So NEXPTIME is *defined* as
the succinct-instance form of NP, and this is an honest and narrow gap: the
library does not prove `NEXPTIME = Σ²₁`, because it does not have the syntax to
state it. NEXPTIME still gets its logical reading – guess a relation over the
expanded universe, check a first-order condition there – its machine problem
and its complete problems, exactly like the other two.

## What is *not* claimed

SO(LFP) = EXPTIME and SO(PFP) = EXPSPACE are **definitions** here, so nothing
is asserted and no capture theorem is being claimed.
[Abiteboul–Vardi–Vianu 1997][abiteboul1997fixpoint] is the reason these are the
right logics to name the classes after, cited as motivation and not as a
theorem proved here; it is stated in the relational (order-free, generic)
setting, which is a second reason not to cite it flatly.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}} [L.IsRelational]

/-! ### The three classes -/

/-- **The class EXPTIME**, defined as SO(≤, LFP) – equivalently, and with no
order in the statement at all, as SO(LFP)
(`DescriptiveComplexity.mem_EXPTIME_iff_solfpDefinableFree`): a least fixed point over a
second-order universe. Equivalently, and by theorem, polynomial time read over
an exponential expansion (`DescriptiveComplexity.EXPTIME_eq_PTIME_exp`).

The three membership closure obligations are borrowed through the bridge
theorem: `DescriptiveComplexity.Exponential.Class` proved them once, for
`ExpDefinable C` at an arbitrary class `C`. -/
noncomputable def EXPTIME : ComplexityClass :=
  .ofMem (fun P => SOLFPDefinable P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => solfpDefinable_congr h)

/-- **The class EXPSPACE**, defined as SO(≤, PFP) – equivalently, and with no
order in the statement at all, as SO(PFP)
(`DescriptiveComplexity.mem_EXPSPACE_iff_sopfpDefinableFree`): a partial fixed point over a
second-order universe. Equivalently, and by theorem, polynomial space read over
an exponential expansion (`DescriptiveComplexity.EXPSPACE_eq_PSPACE_exp`). -/
noncomputable def EXPSPACE : ComplexityClass :=
  .ofMem (fun P => SOPFPDefinable P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => sopfpDefinable_congr h)

/-- **The class NEXPTIME**: NP read over an exponential expansion – guess a
relation over the expanded universe, check a first-order condition there. See
the module docstring for why this one is presented as `NP.exp` rather than as a
fixpoint logic. -/
noncomputable def NEXPTIME : ComplexityClass := NP.exp

/-- coEXPTIME, the complement class of EXPTIME. That it *coincides* with
EXPTIME is `DescriptiveComplexity.EXPTIME_eq_coEXPTIME`. -/
noncomputable abbrev coEXPTIME : ComplexityClass := EXPTIME.compl

/-- coEXPSPACE, the complement class of EXPSPACE; it coincides with EXPSPACE
(`DescriptiveComplexity.EXPSPACE_eq_coEXPSPACE`). -/
noncomputable abbrev coEXPSPACE : ComplexityClass := EXPSPACE.compl

/-- coNEXPTIME, the complement class of NEXPTIME. No coincidence is claimed
here: NEXPTIME is not expected to be closed under complement. -/
noncomputable abbrev coNEXPTIME : ComplexityClass := NEXPTIME.compl

/-! ### Membership, unfolded -/

theorem mem_EXPTIME_iff (P : DecisionProblem L) : P ∈ EXPTIME ↔ SOLFPDefinable P :=
  Iff.rfl

theorem mem_EXPSPACE_iff (P : DecisionProblem L) : P ∈ EXPSPACE ↔ SOPFPDefinable P :=
  Iff.rfl

theorem mem_NEXPTIME_iff (P : DecisionProblem L) : P ∈ NEXPTIME ↔ ExpDefinable NP P :=
  Iff.rfl

/-! ### The bridge theorems

Every later result about the exponential classes is stated about
`EXPTIME`/`EXPSPACE`/`NEXPTIME` and proved by rewriting along these, so that
the work happens once, at `DescriptiveComplexity.ComplexityClass.exp` and an
arbitrary class. -/

/-- **EXPTIME is polynomial time on succinct instances.** -/
theorem EXPTIME_eq_PTIME_exp : EXPTIME = PTIME.exp :=
  ComplexityClass.ext (fun P => solfpDefinable_iff_expDefinable P)
    fun P => cofinalHard_congr_mem (fun Q => solfpDefinable_iff_expDefinable Q) P

/-- **EXPSPACE is polynomial space on succinct instances.** -/
theorem EXPSPACE_eq_PSPACE_exp : EXPSPACE = PSPACE.exp :=
  ComplexityClass.ext (fun P => sopfpDefinable_iff_expDefinable P)
    fun P => cofinalHard_congr_mem (fun Q => sopfpDefinable_iff_expDefinable Q) P

/-- **NEXPTIME is NP on succinct instances**, by definition. -/
theorem NEXPTIME_eq_NP_exp : NEXPTIME = NP.exp := rfl

/-! ### Hardness over relational vocabularies

The shape every hardness proof of the exponential catalog discharges, one per
class; each is `DescriptiveComplexity.cofinalHard_iff` read through the bridge
theorem. -/

theorem hard_EXPTIME_iff (P : DecisionProblem L) :
    EXPTIME.Hard P ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        SOLFPDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

theorem hard_EXPSPACE_iff (P : DecisionProblem L) :
    EXPSPACE.Hard P ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        SOPFPDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

theorem hard_NEXPTIME_iff (P : DecisionProblem L) :
    NEXPTIME.Hard P ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        ExpDefinable NP Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

/-- A problem is EXPTIME-hard as soon as every SO(≤, LFP) definable problem
reduces to it. -/
theorem EXPTIME_hard_of_solfpDefinable (P : DecisionProblem L)
    (h : ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
      SOLFPDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] P)) : EXPTIME.Hard P :=
  (hard_EXPTIME_iff P).mpr h

/-- A problem is EXPSPACE-hard as soon as every SO(≤, PFP) definable problem
reduces to it. -/
theorem EXPSPACE_hard_of_sopfpDefinable (P : DecisionProblem L)
    (h : ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
      SOPFPDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] P)) : EXPSPACE.Hard P :=
  (hard_EXPSPACE_iff P).mpr h

/-- A problem is NEXPTIME-hard as soon as every problem NP-definable over an
expanded universe reduces to it. -/
theorem NEXPTIME_hard_of_expDefinable (P : DecisionProblem L)
    (h : ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
      ExpDefinable NP Q → Nonempty (Q ≤ʳᶠᵒ[≤] P)) : NEXPTIME.Hard P :=
  (hard_NEXPTIME_iff P).mpr h

end DescriptiveComplexity
