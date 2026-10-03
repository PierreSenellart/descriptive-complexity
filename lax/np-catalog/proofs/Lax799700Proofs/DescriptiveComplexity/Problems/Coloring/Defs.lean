/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.FinCases
import Lax799700Proofs.DescriptiveComplexity.Ordered
import Lax799700Proofs.DescriptiveComplexity.Padding
import Lax799700Proofs.DescriptiveComplexity.Problems.Sat
import Lax799700Proofs.DescriptiveComplexity.Problems.ThreeColorability.FromSat
import Lax799700Proofs.DescriptiveComplexity.Problems.ThreeColorability.ToSat
import Lax799700Proofs.DescriptiveComplexity.SecondOrder
import Lax799700Proofs.DescriptiveComplexity.Problems.CliqueFamily.Defs
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

/-!
# The coloring family: definitions

Three problems built on one generic property, `Lax799700Proofs.DescriptiveComplexity.ColorableOn`: a
map into `Fin k` separating the pairs related by a *conflict* relation.

* `Lax799700Proofs.DescriptiveComplexity.KCol k`, on `FirstOrder.Language.graph`-structures: is the
  graph `k`-colorable, for a `k` fixed once and for all? The conflict relation
  is adjacency, so a self-loop makes the instance a no-instance, and
  `Lax799700Proofs.DescriptiveComplexity.kCol_three` identifies `KCol 3` with
  `Lax799700Proofs.DescriptiveComplexity.ThreeCol`.
* `Lax799700Proofs.DescriptiveComplexity.ChromaticNumber`, on `FirstOrder.Language.markedGraph`-structures:
  is the chromatic number at most `k`, where `k` is the cardinality of the
  marked set (`Lax799700Proofs.DescriptiveComplexity.Numbers.Unary`)? This is Karp's CHROMATIC
  NUMBER, with `k` part of the instance rather than of the problem.
* `Lax799700Proofs.DescriptiveComplexity.CliqueCover`, on the same vocabulary: can the vertices be
  covered by at most `k` cliques? A clique cover is a proper coloring of the
  complement graph, so this is the same generic property with the conflict
  relation complemented – which is why one interpretation reduces each of the
  two threshold problems to the other, exactly as in
  `Lax799700Proofs.DescriptiveComplexity.Problems.CliqueFamily`.

## Loops, and why the two threshold problems ignore them

The two marked-graph problems take their conflict relation *off the diagonal*
(`x ≠ y ∧ …`), i.e., they are about the underlying loopless graph, which is the
convention of the clique family on this vocabulary. It is also what makes them
interreducible by edge complementation: complementing off the diagonal is an
involution on loopless graphs, but forgets loops. The price is paid once, in
the reduction from 3-colorability
(`Lax799700Proofs.DescriptiveComplexity.Problems.Coloring.Reductions`), whose input *is* loop-sensitive:
a self-looped vertex is turned into a `K₄`, which no 3-coloring survives.

## The palette form of a threshold

A `k`-coloring with `k` the cardinality of the marked set can equivalently be
given as a map into the marked set itself
(`Lax799700Proofs.DescriptiveComplexity.paletteColorableOn_iff`): the marked elements *are* `k` colors.
This is the form the second-order definitions guess, since it needs only a
binary relation variable, where the number `k` is not available to the
formulas.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The generic property -/

section Generic

variable {A : Type}

/-- A coloring whose palette is the marked set itself: a map into the
`Kp`-marked elements giving distinct values to conflicting elements. -/
def PaletteColorableOn (Cfl : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ col : A → A, (∀ x, Kp (col x)) ∧ ∀ x y, Cfl x y → col x ≠ col y

/-- **Colors are the marked elements**: on a finite universe, colorability
with as many colors as the marked set is colorability *by* the marked set.
This is the bridge between the numeric reading of the threshold and its
second-order rendering, where the coloring is guessed as a binary relation
variable. -/
theorem paletteColorableOn_iff [Finite A] (Cfl : A → A → Prop) (Kp : A → Prop) :
    PaletteColorableOn Cfl Kp ↔ Lax799700.Coloring.ColorableOn Cfl {x | Kp x}.ncard := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have hcard : Fintype.card {x // Kp x} = {x | Kp x}.ncard := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]
    rfl
  let e := Fintype.equivFinOfCardEq hcard
  constructor
  · rintro ⟨col, hcol, hproper⟩
    refine ⟨fun x => e ⟨col x, hcol x⟩, fun x y hxy hc => ?_⟩
    exact hproper x y hxy (congrArg Subtype.val (e.injective hc))
  · rintro ⟨c, hproper⟩
    refine ⟨fun x => (e.symm (c x)).1, fun x => (e.symm (c x)).2, fun x y hxy hc => ?_⟩
    exact hproper x y hxy (e.symm.injective (Subtype.ext hc))

variable {B : Type}

/-- `ColorableOn` transports along an equivalence commuting with the conflict
relations. -/
theorem ColorableOn.of_equiv (u : B ≃ A) {CflB : B → B → Prop} {CflA : A → A → Prop}
    {k : ℕ} (hcfl : ∀ b b', CflB b b' ↔ CflA (u b) (u b')) (h : Lax799700.Coloring.ColorableOn CflB k) :
    Lax799700.Coloring.ColorableOn CflA k := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun a => c (u.symm a), fun x y hxy => ?_⟩
  exact hc (u.symm x) (u.symm y) ((hcfl (u.symm x) (u.symm y)).mpr (by simpa using hxy))

end Generic

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700.Coloring.ColorableOn

export Lax799700Proofs.DescriptiveComplexity.ColorableOn (of_equiv)

end Lax799700.Coloring.ColorableOn

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

/-- `ColorableOn` transports along an equivalence, iff version. -/
theorem ColorableOn.equiv_iff (u : B ≃ A) {CflB : B → B → Prop} {CflA : A → A → Prop}
    {k : ℕ} (hcfl : ∀ b b', CflB b b' ↔ CflA (u b) (u b')) :
    Lax799700.Coloring.ColorableOn CflB k ↔ Lax799700.Coloring.ColorableOn CflA k :=
  ⟨ColorableOn.of_equiv u hcfl,
    ColorableOn.of_equiv u.symm fun a a' => by rw [hcfl]; simp⟩

end Generic

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700.Coloring.ColorableOn

export Lax799700Proofs.DescriptiveComplexity.ColorableOn (equiv_iff)

end Lax799700.Coloring.ColorableOn

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure

section Generic

variable {A : Type}

variable {B : Type}

end Generic

/-! ### `k`-colorability, for a fixed `k` -/

section Fixed

variable (k : ℕ) (V : Type) [Language.graph.Structure V]

end Fixed

private theorem kColorable_of_iso {k : ℕ} {A B : Type} [Language.graph.Structure A]
    [Language.graph.Structure B] (e : A ≃[Language.graph] B) (h : Lax799700.Coloring.KColorable k A) :
    Lax799700.Coloring.KColorable k B :=
  ColorableOn.of_equiv e.toEquiv (fun a b => relMap_equiv₂ e adj a b) h

/-- `k`-colorability is isomorphism-invariant. -/
theorem kColorable_iso {k : ℕ} {A B : Type} [Language.graph.Structure A]
    [Language.graph.Structure B] (e : A ≃[Language.graph] B) :
    Lax799700.Coloring.KColorable k A ↔ Lax799700.Coloring.KColorable k B :=
  ⟨kColorable_of_iso e, kColorable_of_iso e.symm⟩

/-- `k`-colorability, as a problem on `Language.graph`-structures. -/
def KCol (k : ℕ) : Lax904597.Problems.DecisionProblem Language.graph where
  Holds := fun V inst => @Lax799700.Coloring.KColorable k V inst
  iso_invariant := fun e => kColorable_iso e

/-! ### Chromatic number and clique cover, with the threshold in the instance -/

section Conflicts

variable {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]

end Conflicts

section Threshold

variable (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A]

end Threshold

section Iso

variable {A B : Type} [Lax799700.CliqueFamily.markedGraph.Structure A] [Lax799700.CliqueFamily.markedGraph.Structure B]

private theorem mgConflict_map (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) (a b : A) :
    Lax799700.Coloring.MGConflict a b ↔ Lax799700.Coloring.MGConflict (e a) (e b) :=
  and_congr ⟨fun h hab => h (e.injective hab), fun h hab => h (congrArg e hab)⟩
    (relMap_equiv₂ e Lax799700.CliqueFamily.mgAdj a b)

private theorem mgCoConflict_map (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) (a b : A) :
    Lax799700.Coloring.MGCoConflict a b ↔ Lax799700.Coloring.MGCoConflict (e a) (e b) :=
  and_congr ⟨fun h hab => h (e.injective hab), fun h hab => h (congrArg e hab)⟩
    (not_congr (relMap_equiv₂ e Lax799700.CliqueFamily.mgAdj a b))

private theorem ncard_marked_map (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) :
    {x : A | Lax799700.CliqueFamily.MGMarked x}.ncard = {x : B | Lax799700.CliqueFamily.MGMarked x}.ncard :=
  ncard_setOf_equiv e.toEquiv fun a => relMap_equiv₁ e Lax799700.CliqueFamily.mgMarked a

/-- The chromatic-number property is isomorphism-invariant. -/
theorem hasSmallChromaticNumber_iso (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) :
    Lax799700.Coloring.HasSmallChromaticNumber A ↔ Lax799700.Coloring.HasSmallChromaticNumber B := by
  refine and_congr e.toEquiv.finite_iff ?_
  rw [ncard_marked_map e]
  exact ColorableOn.equiv_iff e.toEquiv (mgConflict_map e)

/-- The clique-cover property is isomorphism-invariant. -/
theorem hasSmallCliqueCover_iso (e : A ≃[Lax799700.CliqueFamily.markedGraph] B) :
    Lax799700.Coloring.HasSmallCliqueCover A ↔ Lax799700.Coloring.HasSmallCliqueCover B := by
  refine and_congr e.toEquiv.finite_iff ?_
  rw [ncard_marked_map e]
  exact ColorableOn.equiv_iff e.toEquiv (mgCoConflict_map e)

end Iso

/-- CHROMATIC NUMBER, as a problem on marked graphs: can the graph be properly
colored with as many colors as the marked set has elements? -/
def ChromaticNumber : Lax904597.Problems.DecisionProblem Lax799700.CliqueFamily.markedGraph where
  Holds := fun A inst => @Lax799700.Coloring.HasSmallChromaticNumber A inst
  iso_invariant := fun e => hasSmallChromaticNumber_iso e

/-- CLIQUE COVER, as a problem on marked graphs: can the vertices be covered
by at most as many cliques as the marked set has elements? -/
def CliqueCover : Lax904597.Problems.DecisionProblem Lax799700.CliqueFamily.markedGraph where
  Holds := fun A inst => @Lax799700.Coloring.HasSmallCliqueCover A inst
  iso_invariant := fun e => hasSmallCliqueCover_iso e

end Lax799700Proofs.DescriptiveComplexity


