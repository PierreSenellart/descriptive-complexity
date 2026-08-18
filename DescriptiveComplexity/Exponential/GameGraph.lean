/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.GameKernel
import DescriptiveComplexity.Exponential.GameNode

/-!
# The six questions an interpreted AND/OR graph asks, and their kernels

The road from `DescriptiveComplexity.EXPTIME` to SO-GAME plays the AND/OR graph
an interpretation `I` draws **on the expanded universe**. A node of that graph
is a tag together with `d` points
(`DescriptiveComplexity.ExpExpansion.nodeBlock`), and everything the game ever
has to decide about one or two nodes is one of six first-order questions:

| question | why the game asks it |
|---|---|
| `AGWon x` | the existential player claims the position wins outright |
| `AGUniv x`, `¬AGUniv x` | he claims the position belongs to one player, and must prove it |
| `AGMove x y`, `¬AGMove x y` | he proposes a move, or escapes an illegal one |
| `AGStart x` | the position he starts from is a marked start |

`DescriptiveComplexity.Sub` names the six. None of them is a *sentence* over the
base – a quantifier of `I`'s defining formula ranges over points, so it is
second-order over the base (`DescriptiveComplexity.exists_translate`) – and that
is exactly why they become **phases** rather than conjuncts:
`DescriptiveComplexity.ExpExpansion.exists_paramKernel` turns each into an
alternating prefix over rounds of the point block, which a game plays one move
per round.

What this file settles is the **layout**: the six prefixes have different
lengths, and one game has one block. So the rounds are laid out as

```
0 ‥ d-1     the first node's points        parameters
d ‥ 2d-1    the second node's points       parameters
2d ‥ c-1    padding, points, unread        parameters of the short prefixes
c  ‥ n-1    the play rounds of this prefix
```

with `n = 2 * d + Dm` fixed by the *longest* prefix and `c = n - D` chosen per
question, so that every prefix ends at the same round `n - 1` and the move that
fills round `n - j` is the same for all six
(`DescriptiveComplexity.exists_graphKernels`). Padding at the bottom rather than
at the top is what keeps every kernel a sentence over *one* block: no morphism
between merged blocks of different lengths is ever needed.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The six questions -/

/-- The six first-order questions the game asks about one or two nodes of the
interpreted AND/OR graph. -/
inductive Sub
  /-- The first node wins outright. -/
  | won
  /-- The first node is universal. -/
  | univ
  /-- The first node is not universal. -/
  | notuniv
  /-- There is a move from the first node to the second. -/
  | mv
  /-- There is no move from the first node to the second. -/
  | notmv
  /-- The first node is a marked start. -/
  | st
  deriving DecidableEq

instance : Fintype Sub :=
  ⟨{.won, .univ, .notuniv, .mv, .notmv, .st}, by intro x; cases x <;> simp⟩

namespace ExpExpansion

variable {L : Language.{0, 0}} {X : ExpExpansion L} {T : Type} {d n : ℕ}
variable (I : FOInterpretation (X.E.sum Language.order) Language.andOrGraph T d)

/-! ### A node, read off the rounds -/

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

/-- The node whose tag is `t` and whose points are the argument slot `a` of the
rounds: slot `0` is the first node, slot `1` the second. -/
def nodeAt (h : 2 * d ≤ n) (t : T) (a : Fin 2) (pts : Fin n → X.Map A) :
    I.Map (X.Map A) :=
  (t, fun b => pts (paramIx d n h a b))

/-- **What the six questions ask**, as properties of the rounds. -/
def SubHolds (h : 2 * d ≤ n) (s : Sub) (tx ty : T) (pts : Fin n → X.Map A) : Prop :=
  letI := X.mapLinearOrder A
  letI := I.mapStructure (X.Map A)
  match s with
  | .won => AGWon (nodeAt I h tx 0 pts)
  | .univ => AGUniv (nodeAt I h tx 0 pts)
  | .notuniv => ¬AGUniv (nodeAt I h tx 0 pts)
  | .mv => AGMove (nodeAt I h tx 0 pts) (nodeAt I h ty 1 pts)
  | .notmv => ¬AGMove (nodeAt I h tx 0 pts) (nodeAt I h ty 1 pts)
  | .st => AGStart (nodeAt I h tx 0 pts)

/-! ### The defining formula of each question -/

/-- A defining formula about the first node only, read as one about two. -/
noncomputable def widen (φ : (X.E.sum Language.order).Formula (Fin 1 × Fin d)) :
    (X.E.sum Language.order).Formula (Fin 2 × Fin d) :=
  Formula.relabel (fun p : Fin 1 × Fin d => ((0 : Fin 2), p.2)) φ

/-- **The defining formula of each of the six questions.** -/
noncomputable def subFormula (s : Sub) (tx ty : T) :
    (X.E.sum Language.order).Formula (Fin 2 × Fin d) :=
  match s with
  | .won => widen (I.relFormula agWon ![tx])
  | .univ => widen (I.relFormula agUniv ![tx])
  | .notuniv => ∼(widen (I.relFormula agUniv ![tx]))
  | .mv => I.relFormula agMove ![tx, ty]
  | .notmv => ∼(I.relFormula agMove ![tx, ty])
  | .st => widen (I.relFormula agStart ![tx])

@[simp] theorem subFormula_won (tx ty : T) :
    subFormula I .won tx ty = widen (I.relFormula agWon ![tx]) := rfl

@[simp] theorem subFormula_univ (tx ty : T) :
    subFormula I .univ tx ty = widen (I.relFormula agUniv ![tx]) := rfl

@[simp] theorem subFormula_notuniv (tx ty : T) :
    subFormula I .notuniv tx ty = ∼(widen (I.relFormula agUniv ![tx])) := rfl

@[simp] theorem subFormula_mv (tx ty : T) :
    subFormula I .mv tx ty = I.relFormula agMove ![tx, ty] := rfl

@[simp] theorem subFormula_notmv (tx ty : T) :
    subFormula I .notmv tx ty = ∼(I.relFormula agMove ![tx, ty]) := rfl

@[simp] theorem subFormula_st (tx ty : T) :
    subFormula I .st tx ty = widen (I.relFormula agStart ![tx]) := rfl

/-! ### The formula is the question -/

private theorem realize_widen (φ : (X.E.sum Language.order).Formula (Fin 1 × Fin d))
    (v : Fin 2 × Fin d → X.Map A) :
    letI := X.mapLinearOrder A
    ((widen φ).Realize (M := X.Map A) v ↔
      φ.Realize (M := X.Map A) fun p => v (0, p.2)) := by
  letI := X.mapLinearOrder A
  exact Formula.realize_relabel

private theorem relMap_nodeAt₁ (h : 2 * d ≤ n) (r : Language.andOrGraph.Relations 1)
    (t : T) (pts : Fin n → X.Map A) :
    letI := X.mapLinearOrder A
    letI := I.mapStructure (X.Map A)
    (RelMap r ![nodeAt I h t 0 pts] ↔
      (I.relFormula r ![t]).Realize (M := X.Map A) fun p => pts (paramIx d n h 0 p.2)) := by
  letI := X.mapLinearOrder A
  letI := I.mapStructure (X.Map A)
  refine Iff.trans (I.relMap_map (X.Map A) r _) ?_
  have htag : (fun i => (![nodeAt I h t 0 pts] i).1) = ![t] := by
    funext i
    fin_cases i
    rfl
  have harg : (fun p : Fin 1 × Fin d => (![nodeAt I h t 0 pts] p.1).2 p.2) =
      fun p : Fin 1 × Fin d => pts (paramIx d n h 0 p.2) := by
    funext p
    obtain ⟨i, b⟩ := p
    fin_cases i
    rfl
  rw [htag, harg]

private theorem relMap_nodeAt₂ (h : 2 * d ≤ n) (r : Language.andOrGraph.Relations 2)
    (tx ty : T) (pts : Fin n → X.Map A) :
    letI := X.mapLinearOrder A
    letI := I.mapStructure (X.Map A)
    (RelMap r ![nodeAt I h tx 0 pts, nodeAt I h ty 1 pts] ↔
      (I.relFormula r ![tx, ty]).Realize (M := X.Map A)
        fun p => pts (paramIx d n h p.1 p.2)) := by
  letI := X.mapLinearOrder A
  letI := I.mapStructure (X.Map A)
  refine Iff.trans (I.relMap_map (X.Map A) r _) ?_
  have htag : (fun i => (![nodeAt I h tx 0 pts, nodeAt I h ty 1 pts] i).1) = ![tx, ty] := by
    funext i
    fin_cases i <;> rfl
  have harg : (fun p : Fin 2 × Fin d =>
        (![nodeAt I h tx 0 pts, nodeAt I h ty 1 pts] p.1).2 p.2) =
      fun p : Fin 2 × Fin d => pts (paramIx d n h p.1 p.2) := by
    funext p
    obtain ⟨i, b⟩ := p
    fin_cases i <;> rfl
  rw [htag, harg]

/-- **Each defining formula asks its question.** -/
theorem realize_subFormula (h : 2 * d ≤ n) (s : Sub) (tx ty : T) (pts : Fin n → X.Map A) :
    letI := X.mapLinearOrder A
    ((subFormula I s tx ty).Realize (M := X.Map A)
        (fun p => pts (paramIx d n h p.1 p.2)) ↔ SubHolds I h s tx ty pts) := by
  letI := X.mapLinearOrder A
  letI := I.mapStructure (X.Map A)
  have hw : ∀ r : Language.andOrGraph.Relations 1,
      ((widen (I.relFormula r ![tx])).Realize (M := X.Map A)
          (fun p => pts (paramIx d n h p.1 p.2)) ↔ RelMap r ![nodeAt I h tx 0 pts]) :=
    fun r => (realize_widen (I.relFormula r ![tx])
      (fun p => pts (paramIx d n h p.1 p.2))).trans (relMap_nodeAt₁ I h r tx pts).symm
  have hm : ((I.relFormula agMove ![tx, ty]).Realize (M := X.Map A)
        (fun p => pts (paramIx d n h p.1 p.2)) ↔
      RelMap agMove ![nodeAt I h tx 0 pts, nodeAt I h ty 1 pts]) :=
    (relMap_nodeAt₂ I h agMove tx ty pts).symm
  cases s with
  | won => exact hw agWon
  | univ => exact hw agUniv
  | notuniv => exact Formula.realize_not.trans (not_congr (hw agUniv))
  | mv => exact hm
  | notmv => exact Formula.realize_not.trans (not_congr hm)
  | st => exact hw agStart

/-! ### The six kernels, at one layout -/

/-- **What it is for a kernel to decide a question at a layout**: read against
rounds whose first `c` hold the parameters and whose last `D` are quantified
alternately, it is the question. -/
def KernelSpec (h : 2 * d ≤ n) (c D : ℕ) (s : Sub) (tx ty : T)
    (K : ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence) : Prop :=
  ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    letI := X.mapLinearOrder A
    ∀ (pts : Fin n → X.Map A)
      (ext : (Fin D → X.pointBlock.Assignment A) → (Fin n → X.pointBlock.Assignment A)),
      (∀ τs (k : Fin n), (k : ℕ) < c → ext τs k = pointAssign (pts k)) →
      (∀ τs (i : Fin D) (k : Fin n), (k : ℕ) = c + (i : ℕ) → ext τs k = τs i) →
      (altBlockQuant A X.pointBlock D
          (fun τs => @Sentence.Realize _ A (roundStructure X (ext τs)) K) true ↔
        SubHolds I h s tx ty pts)

variable (X T d)

open Classical in
/-- **The six questions share one block.** Every question gets the same number
`n = 2 * d + Dm` of rounds, `Dm` being the length of the longest of the six
prefixes; a question whose own prefix is shorter simply starts its play rounds
later, at `c = n - D`, so that all six end at round `n - 1` and the move filling
round `n - j` does not depend on which question is being asked. -/
theorem exists_graphKernels [Finite T]
    (I : FOInterpretation (X.E.sum Language.order) Language.andOrGraph T d) :
    ∃ (Dm : ℕ) (D : Sub → T → T → ℕ), (∀ s tx ty, D s tx ty ≤ Dm) ∧
      ∃ K : ∀ (_s : Sub) (_tx _ty : T),
          ((L.sum Language.order).sum (repMerged X.pointBlock (2 * d + Dm)).lang).Sentence,
        ∀ (s : Sub) (tx ty : T),
          KernelSpec I (n := 2 * d + Dm) (by omega)
            (2 * d + Dm - D s tx ty) (D s tx ty) s tx ty (K s tx ty) := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  have hex : ∀ (s : Sub) (tx ty : T), ∃ D : ℕ, ∀ (n c : ℕ) (_hcn : c + D = n) (_h2d : 2 * d ≤ c),
      ∃ K : ((L.sum Language.order).sum (repMerged X.pointBlock n).lang).Sentence,
        ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
          letI := X.mapLinearOrder A
          ∀ (pts : Fin n → X.Map A)
            (ext : (Fin D → X.pointBlock.Assignment A) →
              (Fin n → X.pointBlock.Assignment A)),
            (∀ τs (k : Fin n), (k : ℕ) < c → ext τs k = pointAssign (pts k)) →
            (∀ τs (i : Fin D) (k : Fin n), (k : ℕ) = c + (i : ℕ) → ext τs k = τs i) →
            (altBlockQuant A X.pointBlock D
                (fun τs => @Sentence.Realize _ A (roundStructure X (ext τs)) K) true ↔
              (subFormula I s tx ty).Realize (M := X.Map A) fun p =>
                pts (paramIx d n (by omega) p.1 p.2)) :=
    fun s tx ty => exists_paramKernel X (subFormula I s tx ty)
  choose D₀ hD₀ using hex
  refine ⟨Finset.univ.sup fun p : Sub × T × T => D₀ p.1 p.2.1 p.2.2, D₀, fun s tx ty => ?_, ?_⟩
  · exact Finset.le_sup (f := fun p : Sub × T × T => D₀ p.1 p.2.1 p.2.2)
      (Finset.mem_univ (s, tx, ty))
  · set Dm := Finset.univ.sup fun p : Sub × T × T => D₀ p.1 p.2.1 p.2.2 with hDm
    have hle : ∀ s tx ty, D₀ s tx ty ≤ Dm := fun s tx ty =>
      Finset.le_sup (f := fun p : Sub × T × T => D₀ p.1 p.2.1 p.2.2)
        (Finset.mem_univ (s, tx, ty))
    have hstep : ∀ (s : Sub) (tx ty : T),
        ∃ K : ((L.sum Language.order).sum
            (repMerged X.pointBlock (2 * d + Dm)).lang).Sentence,
          KernelSpec I (n := 2 * d + Dm) (by omega)
            (2 * d + Dm - D₀ s tx ty) (D₀ s tx ty) s tx ty K := by
      intro s tx ty
      have h1 : 2 * d + Dm - D₀ s tx ty + D₀ s tx ty = 2 * d + Dm := by
        have := hle s tx ty; omega
      have h2 : 2 * d ≤ 2 * d + Dm - D₀ s tx ty := by have := hle s tx ty; omega
      obtain ⟨K, hK⟩ := hD₀ s tx ty (2 * d + Dm) (2 * d + Dm - D₀ s tx ty) h1 h2
      refine ⟨K, fun A _ _ _ _ pts ext hfix hemb => ?_⟩
      exact (hK A pts ext hfix hemb).trans (realize_subFormula I (by omega) s tx ty pts)
    choose K hK using hstep
    exact ⟨K, hK⟩

end ExpExpansion

end DescriptiveComplexity
