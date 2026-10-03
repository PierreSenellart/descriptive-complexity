/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lax799700Proofs.DescriptiveComplexity.Block
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Lax799700Proofs.DescriptiveComplexity.Problems.Coloring.Defs
import Lax799700Proofs.DescriptiveComplexity.SecondOrder
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
# The coloring family is existential second-order definable

Membership for the three problems, in two flavors dictated by where the
number of colors lives.

* For `Lax799700Proofs.DescriptiveComplexity.KCol k`, the number `k` is fixed by the problem, so the
  definition can guess the `k` color classes as `k` unary relation variables
  and check first-order that they cover the vertices and that no edge stays
  inside a class (`Lax799700Proofs.DescriptiveComplexity.kCol_sigmaSODefinable`); the kernel is built
  with `Formula.iSup`/`iInf` over `Fin k`.
* For `Lax799700Proofs.DescriptiveComplexity.ChromaticNumber` and `Lax799700Proofs.DescriptiveComplexity.CliqueCover`, the
  number is the size of the marked set, so it is *not* available to the
  formulas – there is no “`k` classes” to write down. The palette form
  (`Lax799700Proofs.DescriptiveComplexity.paletteColorableOn_iff`) removes the problem: coloring with
  as many colors as the marked set has elements is coloring *by* the marked
  set, which a single binary relation variable `Col x y`, read as “`x` has
  color `y`”, expresses. The kernel then has two clauses: every vertex gets
  some marked color, and two conflicting vertices never share a color. Note
  that the guessed relation need not be functional: choosing one color per
  vertex is enough, and the second clause already forbids a shared one.

The two threshold problems differ only in the sign of the adjacency atom in
that second clause, so their kernels come from one builder
(`Lax799700Proofs.DescriptiveComplexity.paletteProperClause`) parameterized by that sign.
-/

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

/-! ### Membership: the color classes as guessed relations -/

section SigmaOne

/-- The single existential block of the `Σ₁` definition of `k`-colorability:
one unary relation variable per color. -/
def colorGuessBlock (k : ℕ) : Lax904597.SecondOrder.SOBlock where
  ι := Fin k
  arity := fun _ => 1

/-- The symbol of the `i`-th color class. -/
def cgColorSym {k : ℕ} (i : Fin k) : (colorGuessBlock k).lang.Relations 1 := ⟨i, rfl⟩

/-- The vocabulary of the kernel: graphs together with the guessed color
classes. -/
abbrev kColSOLang (k : ℕ) : Language := Language.graph.sum (colorGuessBlock k).lang

/-- The adjacency symbol in the kernel's vocabulary. -/
abbrev kcAdjSym (k : ℕ) : (kColSOLang k).Relations 2 := Sum.inl adj

/-- The symbol of the `i`-th color class in the kernel's vocabulary. -/
abbrev kcColorSym {k : ℕ} (i : Fin k) : (kColSOLang k).Relations 1 := Sum.inr (cgColorSym i)

/-- The first-order kernel of the `Σ₁` definition of `k`-colorability: every
vertex belongs to some color class, and no edge has both endpoints in the
same class. -/
noncomputable def kColKernel (k : ℕ) : (kColSOLang k).Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
        (FirstOrder.Language.Formula.iSup
          (fun i : Fin k =>
            FirstOrder.Language.Relations.formula₁ (kcColorSym i) (FirstOrder.Language.Term.var (Sum.inr 0)))) ⊓
      FirstOrder.Language.Formula.iAlls (Fin 2)
        ((FirstOrder.Language.Relations.formula₂ (kcAdjSym k) (FirstOrder.Language.Term.var (Sum.inr 0))
              (FirstOrder.Language.Term.var (Sum.inr 1))).imp
          (FirstOrder.Language.Formula.iInf
            (fun i : Fin k =>
              FirstOrder.Language.BoundedFormula.not
                (FirstOrder.Language.Relations.formula₁ (kcColorSym i) (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
                  FirstOrder.Language.Relations.formula₁ (kcColorSym i) (FirstOrder.Language.Term.var (Sum.inr 1))))))

/-- Realization of the kernel under an assignment of the color classes. -/
private theorem realize_kColKernel {k : ℕ} {V : Type} [Language.graph.Structure V]
    (ρ : (colorGuessBlock k).Assignment V) :
    (@Sentence.Realize (kColSOLang k) V
        (@sumStructure _ _ V _ ((colorGuessBlock k).structure ρ)) (kColKernel k)) ↔
      (∀ x : V, ∃ i : Fin k, ρ i ![x]) ∧
        ∀ x y : V, RelMap adj ![x, y] → ∀ i : Fin k, ¬(ρ i ![x] ∧ ρ i ![y]) := by
  let := (colorGuessBlock k).structure ρ
  have hsub : ∀ (i : Fin k) (w : Fin 1 → V),
      RelMap (L := kColSOLang k) (M := V) (kcColorSym i) w ↔ ρ i w :=
    fun _ _ => Iff.rfl
  rw [kColKernel]
  simp only [Sentence.Realize, Formula.realize_inf, Formula.realize_iAlls,
    Formula.realize_imp, Formula.realize_iSup, Formula.realize_iInf, Formula.realize_not,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr,
    Language.relMap_sumInl, hsub]
  refine and_congr ⟨fun h x => ?_, fun h i => ?_⟩ ⟨fun h x y hxy i => ?_, fun h i hi j => ?_⟩
  · obtain ⟨i, hi⟩ := h fun _ => x
    exact ⟨i, hi⟩
  · obtain ⟨j, hj⟩ := h (i 0)
    exact ⟨j, hj⟩
  · exact h ![x, y] (by simpa using hxy) i
  · exact h (i 0) (i 1) (by simpa using hi) j

/-- **`k`-colorability is `Σ₁`-definable**: existentially guess the `k` color
classes, then check first-order that they cover the vertices and that no edge
stays inside a class. Since NP is defined as `Σ₁`-definability, this is the
membership half of the NP-completeness of `k`-colorability. -/
theorem kCol_sigmaSODefinable (k : ℕ) : Lax904597.SecondOrder.SigmaSODefinable 1 (KCol k) := by
  refine ⟨[colorGuessBlock k], rfl, kColKernel k, ?_⟩
  intro V _ _ _
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun i (w : Fin 1 → V) => c (w 0) = i, (realize_kColKernel _).mpr
      ⟨fun x => ⟨c x, rfl⟩, fun x y hxy i hi => ?_⟩⟩
    exact hc x y hxy (hi.1.trans hi.2.symm)
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hcover, hproper⟩ := (realize_kColKernel ρ).mp hρ
    choose c hcolor using hcover
    exact ⟨c, fun x y hxy hcxy =>
      hproper x y hxy (c x) ⟨hcolor x, hcxy ▸ hcolor y⟩⟩

end SigmaOne

/-! ### Chromatic Number and Clique Cover: the palette as a binary relation -/

section Palette

end Palette

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

/-- The relation variables of the block. -/
inductive PaletteGuessBlockIx where
/-- The guessed coloring: `col x y` reads “`x` has color `y`”. -/

  | col
  deriving DecidableEq

instance : Fintype _root_.Lax799700Proofs.DescriptiveComplexity.PaletteGuessBlockIx :=
  ⟨List.toFinset [.col], by intro x; cases x <;> simp⟩

/-- The single existential block of the `Σ₁` definitions of the two threshold
problems: one binary relation variable, read as “this vertex has that
color”, the colors being the marked elements. -/
def paletteGuessBlock : Lax904597.SecondOrder.SOBlock
    where
  ι := _root_.Lax799700Proofs.DescriptiveComplexity.PaletteGuessBlockIx
  arity := fun i =>
    match i with
    | .col => 2

/-- The vocabulary of the kernel: the instance expanded by the block. -/
abbrev paletteSOLang : FirstOrder.Language :=
  (Lax799700.CliqueFamily.markedGraph).sum (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.paletteGuessBlock)

/-- The `adj` symbol over the sum. -/
abbrev pcAdjSym : (_root_.Lax799700Proofs.DescriptiveComplexity.paletteSOLang).Relations 2 :=
  Sum.inl Lax799700.CliqueFamily.mgAdj

/-- The `marked` symbol over the sum. -/
abbrev pcMarkedSym : (_root_.Lax799700Proofs.DescriptiveComplexity.paletteSOLang).Relations 1 :=
  Sum.inl Lax799700.CliqueFamily.mgMarked

/-- The `col` relation variable. -/
def pcColRel : (Lax904597.SecondOrder.SOBlock.lang _root_.Lax799700Proofs.DescriptiveComplexity.paletteGuessBlock).Relations 2 :=
  ⟨.col, rfl⟩

/-- The `col` symbol over the sum. -/
abbrev pcColSym : (_root_.Lax799700Proofs.DescriptiveComplexity.paletteSOLang).Relations 2 :=
  Sum.inr _root_.Lax799700Proofs.DescriptiveComplexity.pcColRel

end Lax799700Proofs.DescriptiveComplexity

namespace Lax799700Proofs.DescriptiveComplexity

open FirstOrder

open Language Structure Lax904597.SecondOrder.SOBlock

section Palette

/-- Kernel clause: every vertex gets a color, and colors are marked
elements. -/
private noncomputable def paletteTotalClause : paletteSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
      (FirstOrder.Language.Formula.iExs (Fin 1)
        (FirstOrder.Language.Relations.formula₂ pcColSym (FirstOrder.Language.Term.var (Sum.inl (Sum.inr 0)))
            (FirstOrder.Language.Term.var (Sum.inr 0)) ⊓
          FirstOrder.Language.Relations.formula₁ pcMarkedSym (FirstOrder.Language.Term.var (Sum.inr 0))))

/-- Kernel clause: two conflicting vertices never share a color. The flag
selects the conflict relation: adjacency for Chromatic Number,
non-adjacency for Clique Cover. -/
private noncomputable def paletteProperClause (positive : Bool) : paletteSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
      (((FirstOrder.Language.BoundedFormula.not
                  (FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var (Sum.inr 0))
                    (FirstOrder.Language.Term.var (Sum.inr 1))) ⊓
                if positive then
                  FirstOrder.Language.Relations.formula₂ pcAdjSym (FirstOrder.Language.Term.var (Sum.inr 0))
                    (FirstOrder.Language.Term.var (Sum.inr 1))
                else
                  FirstOrder.Language.BoundedFormula.not
                    (FirstOrder.Language.Relations.formula₂ pcAdjSym (FirstOrder.Language.Term.var (Sum.inr 0))
                      (FirstOrder.Language.Term.var (Sum.inr 1)))) ⊓
              FirstOrder.Language.Relations.formula₂ pcColSym (FirstOrder.Language.Term.var (Sum.inr 0))
                (FirstOrder.Language.Term.var (Sum.inr 2)) ⊓
            FirstOrder.Language.Relations.formula₂ pcColSym (FirstOrder.Language.Term.var (Sum.inr 1))
              (FirstOrder.Language.Term.var (Sum.inr 2))).imp
        Bot.bot)

/-- The kernel of the `Σ₁` definition of a threshold coloring problem. -/
noncomputable def paletteKernel (positive : Bool) : paletteSOLang.Sentence :=
  paletteTotalClause ⊓ paletteProperClause positive

/-- Realization of the kernel under an assignment of the coloring. -/
private theorem realize_paletteKernel {A : Type} [Lax799700.CliqueFamily.markedGraph.Structure A]
    (positive : Bool) (ρ : paletteGuessBlock.Assignment A) :
    (@Sentence.Realize paletteSOLang A
        (@sumStructure _ _ A _ (paletteGuessBlock.structure ρ)) (paletteKernel positive)) ↔
      (∀ x : A, ∃ y : A, ρ .col ![x, y] ∧ Lax799700.CliqueFamily.MGMarked y) ∧
        ∀ x x' y : A, x ≠ x' → (if positive then Lax799700.CliqueFamily.MGAdj x x' else ¬Lax799700.CliqueFamily.MGAdj x x') →
          ρ .col ![x, y] → ρ .col ![x', y] → False := by
  let := paletteGuessBlock.structure ρ
  have hsub : ∀ (w : Fin 2 → A),
      RelMap (L := paletteSOLang) (M := A) pcColSym w ↔ ρ .col w := fun _ => Iff.rfl
  rw [paletteKernel]
  cases positive
  · simp only [paletteTotalClause, paletteProperClause, Sentence.Realize,
      Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_iExs,
      Formula.realize_not, Formula.realize_bot, Formula.realize_rel₁, Formula.realize_rel₂,
      Formula.realize_equal, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
      Language.relMap_sumInl, hsub, if_false, Bool.false_eq_true]
    refine and_congr ⟨fun h x => ?_, fun h i => ?_⟩ ⟨fun h x x' y hne hadj h₁ h₂ => ?_,
      fun h i hi => ?_⟩
    · obtain ⟨y, hy1, hy2⟩ := h fun _ => x
      exact ⟨y 0, hy1, hy2⟩
    · obtain ⟨y, hy1, hy2⟩ := h (i 0)
      exact ⟨fun _ => y, hy1, hy2⟩
    · exact h ![x, x', y] ⟨⟨⟨hne, hadj⟩, h₁⟩, h₂⟩
    · exact h (i 0) (i 1) (i 2) hi.1.1.1 hi.1.1.2 hi.1.2 hi.2
  · simp only [paletteTotalClause, paletteProperClause, Sentence.Realize,
      Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_iExs,
      Formula.realize_not, Formula.realize_bot, Formula.realize_rel₁, Formula.realize_rel₂,
      Formula.realize_equal, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
      Language.relMap_sumInl, hsub, if_true]
    refine and_congr ⟨fun h x => ?_, fun h i => ?_⟩ ⟨fun h x x' y hne hadj h₁ h₂ => ?_,
      fun h i hi => ?_⟩
    · obtain ⟨y, hy1, hy2⟩ := h fun _ => x
      exact ⟨y 0, hy1, hy2⟩
    · obtain ⟨y, hy1, hy2⟩ := h (i 0)
      exact ⟨fun _ => y, hy1, hy2⟩
    · exact h ![x, x', y] ⟨⟨⟨hne, hadj⟩, h₁⟩, h₂⟩
    · exact h (i 0) (i 1) (i 2) hi.1.1.1 hi.1.1.2 hi.1.2 hi.2

/-- Both threshold problems are `Σ₁`-definable, by the palette form of their
threshold: guess the coloring as a binary relation into the marked set. -/
private theorem palette_sigmaSODefinable (positive : Bool)
    (P : Lax904597.Problems.DecisionProblem Lax799700.CliqueFamily.markedGraph)
    (hP : ∀ (A : Type) [Lax799700.CliqueFamily.markedGraph.Structure A] [Finite A],
      P A ↔ PaletteColorableOn
        (fun x x' : A => x ≠ x' ∧ (if positive then Lax799700.CliqueFamily.MGAdj x x' else ¬Lax799700.CliqueFamily.MGAdj x x'))
        (Lax799700.CliqueFamily.MGMarked (A := A))) :
    Lax904597.SecondOrder.SigmaSODefinable 1 P := by
  refine ⟨[paletteGuessBlock], rfl, paletteKernel positive, ?_⟩
  intro A _ _ _
  rw [hP A]
  constructor
  · rintro ⟨col, hcol, hproper⟩
    refine ⟨fun i => match i with | .col => fun w : Fin 2 → A => col (w 0) = w 1,
      (realize_paletteKernel _ _).mpr
      ⟨fun x => ⟨col x, rfl, hcol x⟩, fun x x' y hne hadj h₁ h₂ => ?_⟩⟩
    exact hproper x x' ⟨hne, hadj⟩ (h₁.trans h₂.symm)
  · rintro ⟨ρ, hρ⟩
    obtain ⟨htot, hproper⟩ := (realize_paletteKernel _ ρ).mp hρ
    choose col hcol1 hcol2 using htot
    exact ⟨col, hcol2, fun x x' hcfl hcolor =>
      hproper x x' (col x) hcfl.1 hcfl.2 (hcol1 x) (hcolor ▸ hcol1 x')⟩

/-- **Chromatic Number is `Σ₁`-definable**: guess a coloring of the vertices
by the marked elements, and check first-order that every vertex has a marked
color and that no two adjacent vertices share one. -/
theorem chromaticNumber_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 ChromaticNumber :=
  palette_sigmaSODefinable true ChromaticNumber fun A _ _ => by
    rw [show ChromaticNumber A ↔ Lax799700.Coloring.HasSmallChromaticNumber A from Iff.rfl, Lax799700.Coloring.HasSmallChromaticNumber,
      ← paletteColorableOn_iff]
    exact and_iff_right ‹Finite A›

/-- **Clique Cover is `Σ₁`-definable**: the same definition with the
adjacency atom negated – covering by cliques is coloring the complement. -/
theorem cliqueCover_sigmaSODefinable : Lax904597.SecondOrder.SigmaSODefinable 1 CliqueCover :=
  palette_sigmaSODefinable false CliqueCover fun A _ _ => by
    rw [show CliqueCover A ↔ Lax799700.Coloring.HasSmallCliqueCover A from Iff.rfl, Lax799700.Coloring.HasSmallCliqueCover,
      ← paletteColorableOn_iff]
    exact and_iff_right ‹Finite A›

end Palette

end Lax799700Proofs.DescriptiveComplexity


