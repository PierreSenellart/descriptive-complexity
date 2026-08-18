/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CodeHalt.Hardness.Tags
import DescriptiveComplexity.OrderWalk

/-!
# The interpretation that draws an instance as a program

The defining formulas of the reduction `P ≤ᶠᵒ[≤] CODEHALT`, and the
interpretation `DescriptiveComplexity.codeProgInterp` they assemble, of
dimension `DescriptiveComplexity.dimOf V` over the ordered expansion of the
source vocabulary.

Three things make the formulas short.

* **The mark of an element depends only on its tag**
  (`DescriptiveComplexity.ProgTag.mark`), because the two leaves `oneN` and
  `zeroN` are shared and a bit of the input is read as an *edge* – which of
  the two the last chain node points at – rather than as a mark.
* **The guard of an element depends only on its tag** as well: a tag uses
  `DescriptiveComplexity.ProgTag.used` coordinates and the rest are minima
  (`DescriptiveComplexity.canonF` of `DescriptiveComplexity.Padding`), so
  every defining formula is a conjunction of the two guards with a small
  *body* (`DescriptiveComplexity.CodeProgRed.arg1Body`,
  `DescriptiveComplexity.CodeProgRed.arg2Body`).
* **Every body is a walk of the input order**: the immediate successor of a
  coordinate (`DescriptiveComplexity.succF`), its being a maximum, and
  equality of the other coordinates. No lexicographic order and no arithmetic
  on positions appears – that is what nesting the table by coordinate buys.

The section “Characterization of the interpreted relations” reads each
relation of `FirstOrder.Language.code` back through
`DescriptiveComplexity.FOInterpretation.relMap_map`; the two semantic
relations `DescriptiveComplexity.Arg1On` and `DescriptiveComplexity.Arg2On`
are the only interface the correctness proof uses.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

open Nat.Partrec (Code)

namespace CodeProgRed

variable {L : Language.{0, 0}} (V : FinVocab L) (cP : Code)

/-! ### Selecting the coordinates of an argument -/

/-- The coordinates of the only argument of a unary symbol. -/
def sel₀ (j : Fin (dimOf V)) : Fin 1 × Fin (dimOf V) := (0, j)

/-- The coordinates of the first argument of a binary symbol. -/
def selA (j : Fin (dimOf V)) : Fin 2 × Fin (dimOf V) := (0, j)

/-- The coordinates of the second argument of a binary symbol. -/
def selB (j : Fin (dimOf V)) : Fin 2 × Fin (dimOf V) := (1, j)

/-- The first coordinate: the one the numeral chain walks. -/
def fz : Fin (dimOf V) := ⟨0, dimOf_pos V⟩

/-! ### The atomic builders -/

section Atoms

variable {V}

/-- A symbol of the source vocabulary, in the ordered expansion. -/
abbrev srcSym (i : Fin V.numSyms) : (L.sum Language.order).Relations (V.arity i) :=
  Sum.inl (V.sym i)

/-- The symbol `i` of the source vocabulary holds of the first coordinates of
the tuple held by the first argument, as a formula. -/
def relAtF (i : Fin V.numSyms) : (L.sum Language.order).Formula (Fin 2 × Fin (dimOf V)) :=
  Relations.formula (srcSym i) fun j => Term.var (selA V (Fin.castLE (arity_le_dimOf V i) j))

/-- The coordinate `j` of the first argument is a maximum, as a formula. -/
noncomputable def maxAF (j : Fin (dimOf V)) :
    (L.sum Language.order).Formula (Fin 2 × Fin (dimOf V)) := maxF (selA V j)

/-- The coordinate `j` of the second argument is a minimum, as a formula. -/
noncomputable def botBF (j : Fin (dimOf V)) :
    (L.sum Language.order).Formula (Fin 2 × Fin (dimOf V)) := botF (selB V j)

/-- The coordinate `j` of the second argument covers that of the first, as a
formula. -/
noncomputable def succCoF (j : Fin (dimOf V)) :
    (L.sum Language.order).Formula (Fin 2 × Fin (dimOf V)) := succF (selA V j) (selB V j)

variable {A : Type} [L.Structure A] [LinearOrder A] {v : Fin 2 × Fin (dimOf V) → A}

@[simp] theorem realize_relAtF (i : Fin V.numSyms) :
    (relAtF i).Realize v ↔ bitOf V i fun j => v (selA V j) := by
  rw [relAtF, Formula.realize_rel, bitOf]
  simp only [Term.realize_var, relMap_sumInl]

@[simp] theorem realize_maxAF (j : Fin (dimOf V)) :
    (maxAF (V := V) j).Realize v ↔ IsTop (v (selA V j)) := by
  rw [maxAF, realize_maxF]
  exact Iff.rfl

@[simp] theorem realize_botBF (j : Fin (dimOf V)) :
    (botBF (V := V) j).Realize v ↔ IsBot (v (selB V j)) := realize_botF

@[simp] theorem realize_succCoF (j : Fin (dimOf V)) :
    (succCoF (V := V) j).Realize v ↔
      v (selA V j) < v (selB V j) ∧ ∀ a : A, ¬(v (selA V j) < a ∧ a < v (selB V j)) :=
  realize_succF _ _

end Atoms

/-! ### The bodies of the child relations -/

open scoped Classical in
/-- **The body of the first-child relation**, one case per pair of tags. -/
noncomputable def arg1Body :
    ProgTag V cP → ProgTag V cP → (L.sum Language.order).Formula (Fin 2 × Fin (dimOf V))
  | .root, .cp p => if p = codeRootPos cP then ⊤ else ⊥
  | .cp p, .cp q => if sub1 cP p = some q then ⊤ else ⊥
  | .pairN, .numN => botBF (fz V)
  | .numN, .oneN => ⊤
  | .symN i, .chainN i' l => if i = i' ∧ (l : ℕ) = 0 then botBF (fz V) else ⊥
  | .chainN i l, .chainN i' l' =>
      if i = i' ∧ (l' : ℕ) = (l : ℕ) + 1 then eqTupF (selA V) (selB V) else ⊥
  | .chainN i l, .oneN => if (l : ℕ) + 1 = dimOf V then relAtF i else ⊥
  | .chainN i l, .zeroN => if (l : ℕ) + 1 = dimOf V then ∼(relAtF i) else ⊥
  | _, _ => ⊥

open scoped Classical in
/-- **The body of the second-child relation**, one case per pair of tags. -/
noncomputable def arg2Body :
    ProgTag V cP → ProgTag V cP → (L.sum Language.order).Formula (Fin 2 × Fin (dimOf V))
  | .root, .pairN => ⊤
  | .cp p, .cp q => if sub2 cP p = some q then ⊤ else ⊥
  | .pairN, .symN i => if (i : ℕ) = 0 then ⊤ else ⊥
  | .pairN, .zeroN => if V.numSyms = 0 then ⊤ else ⊥
  | .numN, .numN => succCoF (fz V)
  | .numN, .zeroN => maxAF (fz V)
  | .symN i, .symN i' => if (i' : ℕ) = (i : ℕ) + 1 then ⊤ else ⊥
  | .symN i, .zeroN => if (i : ℕ) + 1 = V.numSyms then ⊤ else ⊥
  | .chainN i l, .chainN i' l' =>
      if i = i' ∧ l = l' then succCoF l ⊓ agreeF (l : ℕ) (selA V) (selB V) else ⊥
  | .chainN _ l, .zeroN => maxAF l
  | _, _ => ⊥

/-! ### The defining formulas -/

/-- The guard of a tag on the argument selected by `sel`: the coordinates it
does not use are minima. -/
noncomputable def guardF {γ : Type} (sel : Fin (dimOf V) → γ) (t : ProgTag V cP) :
    (L.sum Language.order).Formula γ :=
  canonF (ProgTag.used t) sel

/-- The mark of a constructor, as a formula: the tag draws it, and the
argument is canonically padded. -/
noncomputable def markF (s : CodeTag) (t : ProgTag V cP) :
    (L.sum Language.order).Formula (Fin 1 × Fin (dimOf V)) :=
  if ProgTag.mark t = s then guardF V cP (sel₀ V) t else ⊥

/-- Being the root, as a formula. -/
noncomputable def rootMarkF (t : ProgTag V cP) :
    (L.sum Language.order).Formula (Fin 1 × Fin (dimOf V)) :=
  match t with
  | .root => guardF V cP (sel₀ V) .root
  | _ => ⊥

/-- The first-child relation, as a formula. -/
noncomputable def arg1F (t t' : ProgTag V cP) :
    (L.sum Language.order).Formula (Fin 2 × Fin (dimOf V)) :=
  guardF V cP (selA V) t ⊓ guardF V cP (selB V) t' ⊓ arg1Body V cP t t'

/-- The second-child relation, as a formula. -/
noncomputable def arg2F (t t' : ProgTag V cP) :
    (L.sum Language.order).Formula (Fin 2 × Fin (dimOf V)) :=
  guardF V cP (selA V) t ⊓ guardF V cP (selB V) t' ⊓ arg2Body V cP t t'

end CodeProgRed

open CodeProgRed

/-! ### The interpretation -/

variable {L : Language.{0, 0}}

/-- **The interpretation drawing an instance as a program**: the root of the
drawn code composes the fixed procedure `cP` with the pair of the numeral of
the universe size and the nest of the tables. -/
noncomputable def codeProgInterp (V : FinVocab L) (cP : Code) :
    FOInterpretation (L.sum Language.order) Language.code (ProgTag V cP) (dimOf V) where
  relFormula {n} R :=
    match n, R with
    | _, .croot => fun τ => rootMarkF V cP (τ 0)
    | _, .czero => fun τ => markF V cP .zero (τ 0)
    | _, .csucc => fun τ => markF V cP .succ (τ 0)
    | _, .cleft => fun τ => markF V cP .left (τ 0)
    | _, .cright => fun τ => markF V cP .right (τ 0)
    | _, .cpair => fun τ => markF V cP .pair (τ 0)
    | _, .ccomp => fun τ => markF V cP .comp (τ 0)
    | _, .cprec => fun τ => markF V cP .prec (τ 0)
    | _, .crfind => fun τ => markF V cP .rfind (τ 0)
    | _, .carg1 => fun τ => arg1F V cP (τ 0) (τ 1)
    | _, .carg2 => fun τ => arg2F V cP (τ 0) (τ 1)

/-! ### The semantics of the drawing -/

section Semantics

variable {V : FinVocab L} {cP : Code} {A : Type} [L.Structure A] [LinearOrder A]

/-- The element of the drawn instance with a given tag and tuple. -/
def progPt (t : ProgTag V cP) (u : Fin (dimOf V) → A) : (codeProgInterp V cP).Map A := (t, u)

omit [L.Structure A] [LinearOrder A] in
theorem exists_progPt (q : (codeProgInterp V cP).Map A) : ∃ t u, q = progPt t u := ⟨q.1, q.2, rfl⟩

/-- **The guard of an element**: the coordinates its tag does not use are
minima. Elements failing it carry no mark and no child, so they draw nothing. -/
def OkOn (t : ProgTag V cP) (u : Fin (dimOf V) → A) : Prop := Canon (ProgTag.used t) u

/-- **The first-child relation of the drawing**, one case per pair of tags. -/
def Arg1On : ProgTag V cP → ProgTag V cP → (Fin (dimOf V) → A) → (Fin (dimOf V) → A) → Prop
  | .root, .cp p, _, _ => p = codeRootPos cP
  | .cp p, .cp q, _, _ => sub1 cP p = some q
  | .pairN, .numN, _, u' => IsBot (u' (fz V))
  | .numN, .oneN, _, _ => True
  | .symN i, .chainN i' l, _, u' => (i = i' ∧ (l : ℕ) = 0) ∧ IsBot (u' (fz V))
  | .chainN i l, .chainN i' l', u, u' => (i = i' ∧ (l' : ℕ) = (l : ℕ) + 1) ∧ u' = u
  | .chainN i l, .oneN, u, _ => (l : ℕ) + 1 = dimOf V ∧ bitOf V i u
  | .chainN i l, .zeroN, u, _ => (l : ℕ) + 1 = dimOf V ∧ ¬bitOf V i u
  | _, _, _, _ => False

/-- **The second-child relation of the drawing**, one case per pair of
tags. -/
def Arg2On : ProgTag V cP → ProgTag V cP → (Fin (dimOf V) → A) → (Fin (dimOf V) → A) → Prop
  | .root, .pairN, _, _ => True
  | .cp p, .cp q, _, _ => sub2 cP p = some q
  | .pairN, .symN i, _, _ => (i : ℕ) = 0
  | .pairN, .zeroN, _, _ => V.numSyms = 0
  | .numN, .numN, u, u' =>
      u (fz V) < u' (fz V) ∧ ∀ a : A, ¬(u (fz V) < a ∧ a < u' (fz V))
  | .numN, .zeroN, u, _ => IsTop (u (fz V))
  | .symN i, .symN i', _, _ => (i' : ℕ) = (i : ℕ) + 1
  | .symN i, .zeroN, _, _ => (i : ℕ) + 1 = V.numSyms
  | .chainN i l, .chainN i' l', u, u' =>
      (i = i' ∧ l = l') ∧ (u l < u' l ∧ ∀ a : A, ¬(u l < a ∧ a < u' l)) ∧ Agree (l : ℕ) u u'
  | .chainN _ l, .zeroN, u, _ => IsTop (u l)
  | _, _, _, _ => False

end Semantics

/-! ### Characterization of the interpreted relations -/

section Characterizations

variable {V : FinVocab L} {cP : Code} {A : Type} [L.Structure A] [LinearOrder A]

private theorem realize_guardF_sel₀ (t : ProgTag V cP) (u : Fin (dimOf V) → A)
    (v : Fin 1 × Fin (dimOf V) → A) (hv : ∀ j, v (sel₀ V j) = u j) :
    (guardF V cP (sel₀ V) t).Realize v ↔ OkOn t u := by
  rw [guardF, realize_canonF, OkOn]
  exact iff_of_eq (congrArg (Canon (ProgTag.used t)) (funext hv))

private theorem realize_guardF_selA (t : ProgTag V cP) (u : Fin (dimOf V) → A)
    (v : Fin 2 × Fin (dimOf V) → A) (hv : ∀ j, v (selA V j) = u j) :
    (guardF V cP (selA V) t).Realize v ↔ OkOn t u := by
  rw [guardF, realize_canonF, OkOn]
  exact iff_of_eq (congrArg (Canon (ProgTag.used t)) (funext hv))

private theorem realize_guardF_selB (t : ProgTag V cP) (u : Fin (dimOf V) → A)
    (v : Fin 2 × Fin (dimOf V) → A) (hv : ∀ j, v (selB V j) = u j) :
    (guardF V cP (selB V) t).Realize v ↔ OkOn t u := by
  rw [guardF, realize_canonF, OkOn]
  exact iff_of_eq (congrArg (Canon (ProgTag.used t)) (funext hv))

theorem realize_arg1Body (t t' : ProgTag V cP) (u u' : Fin (dimOf V) → A)
    (v : Fin 2 × Fin (dimOf V) → A) (hA : ∀ j, v (selA V j) = u j)
    (hB : ∀ j, v (selB V j) = u' j) :
    (arg1Body V cP t t').Realize v ↔ Arg1On t t' u u' := by
  have hAf : (fun j => v (selA V j)) = u := funext hA
  have hBf : (fun j => v (selB V j)) = u' := funext hB
  classical
  cases t <;> cases t' <;>
    simp only [arg1Body, Arg1On] <;> (try split_ifs with h) <;>
    simp_all [Formula.realize_not]

theorem realize_arg2Body (t t' : ProgTag V cP) (u u' : Fin (dimOf V) → A)
    (v : Fin 2 × Fin (dimOf V) → A) (hA : ∀ j, v (selA V j) = u j)
    (hB : ∀ j, v (selB V j) = u' j) :
    (arg2Body V cP t t').Realize v ↔ Arg2On t t' u u' := by
  have hAf : (fun j => v (selA V j)) = u := funext hA
  have hBf : (fun j => v (selB V j)) = u' := funext hB
  classical
  cases t <;> cases t' <;>
    simp only [arg2Body, Arg2On] <;> (try split_ifs with h) <;>
    simp_all [Formula.realize_inf]

theorem cRoot_pt (t : ProgTag V cP) (u : Fin (dimOf V) → A) :
    CRoot (progPt t u) ↔ OkOn t u ∧ t = ProgTag.root := by
  rw [CRoot, FOInterpretation.relMap_map]
  change (rootMarkF V cP t).Realize _ ↔ _
  cases t
  case root =>
    simp only [rootMarkF]
    exact (realize_guardF_sel₀ _ u _ fun _ => rfl).trans (by simp)
  all_goals exact iff_of_false (by simp [rootMarkF]) (by simp)

theorem mark_pt (s : CodeTag) (t : ProgTag V cP) (u : Fin (dimOf V) → A) :
    Mark s (progPt t u) ↔ OkOn t u ∧ ProgTag.mark t = s := by
  have hkey : ∀ (φ : Language.code.Relations 1) (hφ : ∀ (τ : Fin 1 → ProgTag V cP),
      (codeProgInterp V cP).relFormula φ τ = markF V cP s (τ 0)),
      (RelMap φ ![progPt t u] : Prop) ↔ OkOn t u ∧ ProgTag.mark t = s := by
    intro φ hφ
    rw [FOInterpretation.relMap_map, hφ]
    change (markF V cP s t).Realize _ ↔ _
    by_cases h : ProgTag.mark t = s
    · rw [markF, if_pos h]
      refine Iff.trans (realize_guardF_sel₀ t u _ fun _ => rfl) ?_
      exact ⟨fun hh => ⟨hh, h⟩, fun hh => hh.1⟩
    · rw [markF, if_neg h]
      exact iff_of_false (by simp) (fun hh => h hh.2)
  cases s
  · exact hkey cZero fun _ => rfl
  · exact hkey cSucc fun _ => rfl
  · exact hkey cLeft fun _ => rfl
  · exact hkey cRight fun _ => rfl
  · exact hkey cPair fun _ => rfl
  · exact hkey cComp fun _ => rfl
  · exact hkey cPrec fun _ => rfl
  · exact hkey cRfind fun _ => rfl

theorem cArg1_pt (t t' : ProgTag V cP) (u u' : Fin (dimOf V) → A) :
    CArg1 (progPt t u) (progPt t' u') ↔ OkOn t u ∧ OkOn t' u' ∧ Arg1On t t' u u' := by
  rw [CArg1, FOInterpretation.relMap_map]
  change (arg1F V cP t t').Realize _ ↔ _
  rw [arg1F, Formula.realize_inf, Formula.realize_inf,
    realize_guardF_selA t u _ fun _ => rfl, realize_guardF_selB t' u' _ fun _ => rfl,
    realize_arg1Body t t' u u' _ (fun _ => rfl) fun _ => rfl, and_assoc]

theorem cArg2_pt (t t' : ProgTag V cP) (u u' : Fin (dimOf V) → A) :
    CArg2 (progPt t u) (progPt t' u') ↔ OkOn t u ∧ OkOn t' u' ∧ Arg2On t t' u u' := by
  rw [CArg2, FOInterpretation.relMap_map]
  change (arg2F V cP t t').Realize _ ↔ _
  rw [arg2F, Formula.realize_inf, Formula.realize_inf,
    realize_guardF_selA t u _ fun _ => rfl, realize_guardF_selB t' u' _ fun _ => rfl,
    realize_arg2Body t t' u u' _ (fun _ => rfl) fun _ => rfl, and_assoc]

end Characterizations

end DescriptiveComplexity
