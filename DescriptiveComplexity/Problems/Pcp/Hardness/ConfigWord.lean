/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.MachinesUnbounded
import DescriptiveComplexity.Problems.Pcp.Hardness.History

/-!
# Configurations as words: the rewriting system of a machine

The middle layer of the RE-hardness of `DescriptiveComplexity.PCP`: a machine
on the unbounded tape of `DescriptiveComplexity.MachinesUnbounded` accepts
exactly when the string-rewriting system read off its transition table derives
the halting word from the start word
(`DescriptiveComplexity.HaltPcp.acceptsU_iff_derives`). Composed with
`DescriptiveComplexity.Pcp.History.hasMatch_iff` one file up, this makes the
domino system of the machine decide its acceptance; the sibling `Interp` file
draws that domino system as a first-order interpretation.

## The words

A configuration is written as a word over
`DescriptiveComplexity.HaltPcp.TapeLetter`: a left endmarker, the symbols of a
finite *window* of consecutive tape cells with the state letter wedged in
front of the head's cell, and a right endmarker
(`DescriptiveComplexity.HaltPcp.Represents`). The window must contain the head
and every non-blank cell, and may contain any amount of blank padding beyond
them – a configuration has many words, which is what lets the rules extend the
window on demand.

The format is kept **strict**: the state letter always has a symbol letter to
its right (the cell the head is on). Each rule of
`DescriptiveComplexity.HaltPcp.MRule` preserves strictness on its own – the
boundary variants of the two moves extend the window by one blank cell in the
same rewriting step – so every word of a derivation between the boot and the
halting letter is a configuration word, and the backward reading of a
derivation is a plain case analysis on the rule applied.

## The rules

* the two **moves**, each in a running variant and a boundary variant that
  writes a blank into the cell entering the window. A transition's attributes
  are relations, not functions, so the rules are indexed by the attribute
  values, with the transition existentially quantified in the side condition;
* **boot**: the start word carries a boot letter in the state slot, and a rule
  per start state replaces it. This is what lets the single start domino of
  the PCP construction serve a machine with several start states;
* **halting**: a rule per accepting state replaces the state letter by the
  halting letter, and two-letter erasers then melt the rest of the word away.
  Both sides of every rule are nonempty, as the domino construction requires –
  erasure consumes a neighbouring letter instead of producing the empty word.

No letter of a configuration word is a boot or halting letter, so the boot
rule fires only on the start word and the erasers only after an accepting
state was seen: the phases of a derivation cannot mix.
-/

namespace DescriptiveComplexity

namespace HaltPcp

/-! ### The alphabet -/

/-- The alphabet configurations are written in: the two endmarkers of the
window, the boot letter standing in the state slot of the start word, the
halting letter, and a symbol letter and a state letter per element of the
machine. -/
inductive TapeLetter (A : Type) where
  /-- The left endmarker of the window. -/
  | lft : TapeLetter A
  /-- The right endmarker of the window. -/
  | rgt : TapeLetter A
  /-- The boot letter, in the state slot of the start word. -/
  | boot : TapeLetter A
  /-- The halting letter, the one-letter word a derivation must reach. -/
  | halt : TapeLetter A
  /-- The contents of a tape cell. -/
  | sym : A → TapeLetter A
  /-- The current state, wedged before the head's cell. -/
  | state : A → TapeLetter A

variable {A : Type}

/-- Being a state letter, as a Boolean – the alphabet has no decidable
equality to offer, but the constructor is decidable on its own. -/
def TapeLetter.isState : TapeLetter A → Bool
  | .state _ => true
  | _ => false

/-- A letter of the words below is never a boot or halting letter; this is
the shape the case analyses need. -/
theorem TapeLetter.absurd_of_ne {P : Prop} {a b : TapeLetter A} (h : a = b)
    (hne : a ≠ b := by simp) : P := absurd h hne

/-! ### The rules -/

/-- **The rewriting system of a machine**: the two moves with their boundary
variants, the boot rule, and the halting rule with its erasers. The
transition performing a move is existentially quantified in the side
condition, since its attributes are relations rather than functions; the
letters of the rule are the attribute values themselves. -/
inductive MRule (M : TMData A) : List (TapeLetter A) → List (TapeLetter A) → Prop where
  /-- The boot letter becomes a start state. -/
  | boot {q : A} : M.Start q →
      MRule M [.boot] [.state q]
  /-- A right move with the head staying inside the window: the letter beyond
  the head is carried along unchanged. -/
  | moveR {τ q a b q' c : A} : M.Tr τ → M.Right τ → M.Src τ q → M.Read τ a →
      M.Dst τ q' → M.Write τ b →
      MRule M [.state q, .sym a, .sym c] [.sym b, .state q', .sym c]
  /-- A right move at the right edge of the window: the cell entering the
  window is blank. -/
  | moveREnd {τ q a b q' bk : A} : M.Tr τ → M.Right τ → M.Src τ q → M.Read τ a →
      M.Dst τ q' → M.Write τ b → M.Blank bk →
      MRule M [.state q, .sym a, .rgt] [.sym b, .state q', .sym bk, .rgt]
  /-- A left move with the head staying inside the window. -/
  | moveL {τ q a b q' c : A} : M.Tr τ → ¬M.Right τ → M.Src τ q → M.Read τ a →
      M.Dst τ q' → M.Write τ b →
      MRule M [.sym c, .state q, .sym a] [.state q', .sym c, .sym b]
  /-- A left move at the left edge of the window: the cell entering the
  window is blank. -/
  | moveLEnd {τ q a b q' bk : A} : M.Tr τ → ¬M.Right τ → M.Src τ q → M.Read τ a →
      M.Dst τ q' → M.Write τ b → M.Blank bk →
      MRule M [.lft, .state q, .sym a] [.lft, .state q', .sym bk, .sym b]
  /-- An accepting state becomes the halting letter. -/
  | acc {q : A} : M.Acc q →
      MRule M [.state q] [.halt]
  /-- The halting letter swallows the symbol to its left. -/
  | eraseSymL (c : A) : MRule M [.sym c, .halt] [.halt]
  /-- The halting letter swallows the left endmarker. -/
  | eraseLft : MRule M [.lft, .halt] [.halt]
  /-- The halting letter swallows the symbol to its right. -/
  | eraseSymR (c : A) : MRule M [.halt, .sym c] [.halt]
  /-- The halting letter swallows the right endmarker. -/
  | eraseRgt : MRule M [.halt, .rgt] [.halt]

variable {M : TMData A}

/-- No side of a rule is empty – the promise the domino construction
requires. -/
theorem mRule_ne {l r : List (TapeLetter A)} (h : MRule M l r) : l ≠ [] ∧ r ≠ [] := by
  cases h <;> exact ⟨by simp, by simp⟩

/-! ### The order of the cells

The cells `ℤ × A` are ordered lexicographically – pages first, the machine's
order on the offsets inside a page – and one
`DescriptiveComplexity.TMData.SuccCell` step increases that order strictly.
This is what makes a window a duplicate-free list and puts a cell entering it
outside of it. -/

variable (M) in
/-- The strict lexicographic order on cells. -/
def CellLt (x y : ℤ × A) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ M.Le x.2 y.2 ∧ x.2 ≠ y.2)

theorem CellLt.trans (hlin : IsLinOrd M.Le) {x y z : ℤ × A}
    (hxy : CellLt M x y) (hyz : CellLt M y z) : CellLt M x z := by
  rcases hxy with h1 | ⟨h1, h2, h3⟩ <;> rcases hyz with h4 | ⟨h4, h5, h6⟩
  · exact Or.inl (h1.trans h4)
  · exact Or.inl (h4 ▸ h1)
  · exact Or.inl (h1 ▸ h4)
  · refine Or.inr ⟨h1.trans h4, hlin.2.1 _ _ _ h2 h5, fun hcon => ?_⟩
    exact h3 (hlin.2.2.1 _ _ h2 (hcon ▸ h5))

theorem CellLt.ne {x y : ℤ × A} (h : CellLt M x y) : x ≠ y := by
  rintro rfl
  rcases h with h | ⟨-, -, h⟩
  · exact absurd h (lt_irrefl _)
  · exact h rfl

theorem cellLt_of_succCell {x y : ℤ × A} (h : M.SuccCell x y) : CellLt M x y := by
  rcases h with ⟨hz, hp⟩ | ⟨hz, -, -⟩
  · exact Or.inr ⟨hz.symm, hp.2.2.1, hp.2.2.2.1⟩
  · exact Or.inl (by omega)

/-- A chain of successive cells is duplicate-free and increasing. -/
theorem pairwise_cellLt_of_isChain (hlin : IsLinOrd M.Le) :
    ∀ {l : List (ℤ × A)}, l.IsChain M.SuccCell → l.Pairwise (CellLt M)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | x :: y :: l, h => by
    rw [List.isChain_cons_cons] at h
    have ih := pairwise_cellLt_of_isChain hlin h.2
    have hxy : CellLt M x y := cellLt_of_succCell h.1
    rw [List.pairwise_cons]
    refine ⟨fun z hz => ?_, ih⟩
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hxy
    · exact hxy.trans hlin ((List.pairwise_cons.mp ih).1 z hz)

/-! ### Every cell has a next one and a previous one

On a well-formed machine with at least one position, the strip of pages is
unbounded in both directions: the mirror-image lemmas of
`DescriptiveComplexity.exists_predPos` supply the missing successor facts. -/

section CellSteps

variable [Finite A]

omit [Finite A] in
/-- `SuccPos` mirrors along the reversed order. -/
theorem succPos_reverse {Le : A → A → Prop} {Posn : A → Prop} {p q : A} :
    SuccPos (fun a b => Le b a) Posn p q ↔ SuccPos Le Posn q p := by
  constructor
  · rintro ⟨hp, hq, hle, hne, hbet⟩
    exact ⟨hq, hp, hle, hne.symm, fun r hr h1 h2 => (hbet r hr h2 h1).symm⟩
  · rintro ⟨hp, hq, hle, hne, hbet⟩
    exact ⟨hq, hp, hle, hne.symm, fun r hr h1 h2 => (hbet r hr h2 h1).symm⟩

/-- Every position that is not the highest has one immediately above it. -/
theorem exists_succPos {Le : A → A → Prop} {Posn : A → Prop} (hlin : IsLinOrd Le) {p : A}
    (hp : Posn p) (hmax : ¬MaxPos Le Posn p) : ∃ q, SuccPos Le Posn p q := by
  have hmin : ¬MinPos (fun a b => Le b a) Posn p := fun h => hmax ⟨h.1, h.2⟩
  obtain ⟨q, hq⟩ := exists_predPos hlin.reverse hp hmin
  exact ⟨q, succPos_reverse.mp hq⟩

/-- Every cell over a position has a next cell. -/
theorem exists_succCell (hwf : M.WellFormed) {x : ℤ × A} (hx : M.Posn x.2) :
    ∃ y, M.SuccCell x y := by
  by_cases hmax : MaxPos M.Le M.Posn x.2
  · obtain ⟨p, hp⟩ := exists_minPos hwf.1 hwf.2.1
    exact ⟨(x.1 + 1, p), Or.inr ⟨rfl, hmax, hp⟩⟩
  · obtain ⟨q, hq⟩ := exists_succPos hwf.1 hx hmax
    exact ⟨(x.1, q), Or.inl ⟨rfl, hq⟩⟩

/-- Every cell over a position has a previous cell. -/
theorem exists_predCell (hwf : M.WellFormed) {x : ℤ × A} (hx : M.Posn x.2) :
    ∃ y, M.SuccCell y x := by
  by_cases hmin : MinPos M.Le M.Posn x.2
  · obtain ⟨p, hp⟩ := exists_maxPos hwf.1 hwf.2.1
    exact ⟨(x.1 - 1, p), Or.inr ⟨by omega, hp, hmin⟩⟩
  · obtain ⟨q, hq⟩ := exists_predPos hwf.1 hx hmin
    exact ⟨(x.1, q), Or.inl ⟨rfl, hq⟩⟩

omit [Finite A] in
/-- Lowest positions are unique. -/
theorem minPos_unique {Le : A → A → Prop} {Posn : A → Prop} (hlin : IsLinOrd Le) {p q : A}
    (hp : MinPos Le Posn p) (hq : MinPos Le Posn q) : p = q :=
  hlin.2.2.1 _ _ (hp.2 q hq.1) (hq.2 p hp.1)

omit [Finite A] in
/-- Highest positions are unique. -/
theorem maxPos_unique {Le : A → A → Prop} {Posn : A → Prop} (hlin : IsLinOrd Le) {p q : A}
    (hp : MaxPos Le Posn p) (hq : MaxPos Le Posn q) : p = q :=
  hlin.2.2.1 _ _ (hq.2 p hp.1) (hp.2 q hq.1)

omit [Finite A] in
/-- The element immediately above a given one is unique. -/
theorem succPos_right_unique {Le : A → A → Prop} {Posn : A → Prop} (hlin : IsLinOrd Le)
    {p q q' : A} (h : SuccPos Le Posn p q) (h' : SuccPos Le Posn p q') : q = q' :=
  succPos_left_unique (Posn := Posn) hlin.reverse
    (succPos_reverse.mpr h) (succPos_reverse.mpr h')

omit [Finite A] in
/-- A position with a successor is not the highest. -/
theorem succPos_not_maxPos {Le : A → A → Prop} {Posn : A → Prop} (hlin : IsLinOrd Le)
    {p q : A} (h : SuccPos Le Posn p q) : ¬MaxPos Le Posn p := by
  rintro ⟨-, hmax⟩
  exact h.2.2.2.1 (hlin.2.2.1 _ _ h.2.2.1 (hmax q h.2.1))

omit [Finite A] in
/-- A position with a predecessor is not the lowest. -/
theorem succPos_not_minPos {Le : A → A → Prop} {Posn : A → Prop} (hlin : IsLinOrd Le)
    {p q : A} (h : SuccPos Le Posn p q) : ¬MinPos Le Posn q := by
  rintro ⟨-, hmin⟩
  exact h.2.2.2.1 (hlin.2.2.1 _ _ h.2.2.1 (hmin p h.1))

omit [Finite A] in
/-- The cell after a given one is unique. -/
theorem succCell_right_unique (hwf : M.WellFormed) {x y y' : ℤ × A}
    (h : M.SuccCell x y) (h' : M.SuccCell x y') : y = y' := by
  rcases h with ⟨hz, hp⟩ | ⟨hz, hmax, hmin⟩ <;>
    rcases h' with ⟨hz', hp'⟩ | ⟨hz', hmax', hmin'⟩
  · exact Prod.ext (hz.trans hz'.symm) (succPos_right_unique hwf.1 hp hp')
  · exact absurd hmax' (succPos_not_maxPos hwf.1 hp)
  · exact absurd hmax (succPos_not_maxPos hwf.1 hp')
  · exact Prod.ext (hz.trans hz'.symm) (minPos_unique hwf.1 hmin hmin')

omit [Finite A] in
/-- The cell before a given one is unique. -/
theorem succCell_left_unique (hwf : M.WellFormed) {x x' y : ℤ × A}
    (h : M.SuccCell x y) (h' : M.SuccCell x' y) : x = x' := by
  rcases h with ⟨hz, hp⟩ | ⟨hz, hmax, hmin⟩ <;>
    rcases h' with ⟨hz', hp'⟩ | ⟨hz', hmax', hmin'⟩
  · exact Prod.ext (by omega) (succPos_left_unique hwf.1 hp hp')
  · exact absurd hmin' (succPos_not_minPos hwf.1 hp)
  · exact absurd hmin (succPos_not_minPos hwf.1 hp')
  · exact Prod.ext (by omega) (maxPos_unique hwf.1 hmax hmax')

omit [Finite A] in
/-- The successor cell keeps to the positions. -/
theorem posn_of_succCell {x y : ℤ × A} (h : M.SuccCell x y) : M.Posn y.2 := by
  rcases h with ⟨-, hp⟩ | ⟨-, -, hmin⟩
  · exact hp.2.1
  · exact hmin.1

omit [Finite A] in
/-- The previous cell keeps to the positions, too. -/
theorem posn_of_succCell_left {x y : ℤ × A} (h : M.SuccCell x y) : M.Posn x.2 := by
  rcases h with ⟨-, hp⟩ | ⟨-, hmax, -⟩
  · exact hp.1
  · exact hmax.1

end CellSteps

/-! ### Configuration words

A configuration is written as a window of consecutive cells: the symbols they
hold, with the state letter wedged before the head's cell and an endmarker at
each end. The window contains the head and every non-blank cell over a
position; it may contain blank padding beyond them, so a configuration has
many words. -/

open Pcp

/-- The symbol letters of a list of cells. -/
def cellSyms (c : ConfigU A) (l : List (ℤ × A)) : List (TapeLetter A) :=
  l.map fun x => TapeLetter.sym (c.tape x)

@[simp] theorem cellSyms_nil (c : ConfigU A) : cellSyms c [] = [] := rfl

@[simp] theorem cellSyms_cons (c : ConfigU A) (x : ℤ × A) (l : List (ℤ × A)) :
    cellSyms c (x :: l) = TapeLetter.sym (c.tape x) :: cellSyms c l := rfl

@[simp] theorem cellSyms_append (c : ConfigU A) (l l' : List (ℤ × A)) :
    cellSyms c (l ++ l') = cellSyms c l ++ cellSyms c l' := by
  simp [cellSyms]

/-- Two configurations agreeing on a window write it the same way. -/
theorem cellSyms_congr {c c' : ConfigU A} {l : List (ℤ × A)}
    (h : ∀ x ∈ l, c'.tape x = c.tape x) : cellSyms c' l = cellSyms c l :=
  List.map_congr_left fun x hx => by rw [h x hx]

variable (M) in
/-- **`w` is a word of the configuration `c`**: the symbols of a window of
consecutive cells between the two endmarkers, the state letter wedged before
the head's cell. The window consists of cells over positions, contains the
head, and every cell over a position outside it is blank. -/
def Represents (w : List (TapeLetter A)) (c : ConfigU A) : Prop :=
  ∃ ls rs : List (ℤ × A),
    w = (TapeLetter.lft :: cellSyms c ls) ++ TapeLetter.state c.state ::
        TapeLetter.sym (c.tape c.head) :: (cellSyms c rs ++ [TapeLetter.rgt]) ∧
    (ls ++ c.head :: rs).IsChain M.SuccCell ∧
    (∀ x ∈ ls ++ c.head :: rs, M.Posn x.2) ∧
    ∀ z p, M.Posn p → (z, p) ∉ ls ++ c.head :: rs → M.Blank (c.tape (z, p))

/-! ### Letters of a configuration word

A configuration word carries no boot and no halting letter, and exactly one
state letter; these two facts drive the case analysis on a rewriting step. -/

@[simp] theorem isState_lft : (TapeLetter.lft (A := A)).isState = false := rfl

@[simp] theorem isState_rgt : (TapeLetter.rgt (A := A)).isState = false := rfl

@[simp] theorem isState_boot : (TapeLetter.boot (A := A)).isState = false := rfl

@[simp] theorem isState_halt : (TapeLetter.halt (A := A)).isState = false := rfl

@[simp] theorem isState_sym (a : A) : (TapeLetter.sym a).isState = false := rfl

@[simp] theorem isState_state (q : A) : (TapeLetter.state q).isState = true := rfl

/-- The number of state letters of a word. -/
def stateCount (l : List (TapeLetter A)) : ℕ := l.countP TapeLetter.isState

@[simp] theorem stateCount_nil : stateCount ([] : List (TapeLetter A)) = 0 := rfl

theorem stateCount_append (l l' : List (TapeLetter A)) :
    stateCount (l ++ l') = stateCount l + stateCount l' :=
  List.countP_append

theorem stateCount_cons (a : TapeLetter A) (l : List (TapeLetter A)) :
    stateCount (a :: l) = stateCount l + if a.isState then 1 else 0 :=
  List.countP_cons

@[simp] theorem stateCount_cellSyms (c : ConfigU A) (l : List (ℤ × A)) :
    stateCount (cellSyms c l) = 0 :=
  List.countP_eq_zero.mpr fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
    simp

/-- A word without state letters is exactly a word of vanishing state
count. -/
theorem stateCount_eq_zero {l : List (TapeLetter A)} :
    stateCount l = 0 ↔ ∀ x ∈ l, x.isState = false := by
  rw [stateCount, List.countP_eq_zero]
  exact ⟨fun h x hx => Bool.not_eq_true _ ▸ (by simpa using h x hx),
    fun h x hx => by simp [h x hx]⟩

/-- **Alignment at the state letter**: two decompositions of one word around a
state letter, neither prefix carrying one, agree. -/
theorem state_align : ∀ {u₁ u₂ v₁ v₂ : List (TapeLetter A)} {q₁ q₂ : A},
    u₁ ++ TapeLetter.state q₁ :: v₁ = u₂ ++ TapeLetter.state q₂ :: v₂ →
    (∀ x ∈ u₁, x.isState = false) → (∀ x ∈ u₂, x.isState = false) →
    u₁ = u₂ ∧ q₁ = q₂ ∧ v₁ = v₂
  | [], [], v₁, v₂, q₁, q₂, h, _, _ => by
    simp only [List.nil_append] at h
    injection h with h1 h2
    injection h1 with hq
    exact ⟨rfl, hq, h2⟩
  | [], b :: u₂, v₁, v₂, q₁, q₂, h, _, h₂ => by
    simp only [List.nil_append, List.cons_append] at h
    injection h with h1 _
    have := h₂ b List.mem_cons_self
    rw [← h1] at this
    simp at this
  | a :: u₁, [], v₁, v₂, q₁, q₂, h, h₁, _ => by
    simp only [List.nil_append, List.cons_append] at h
    injection h with h1 _
    have := h₁ a List.mem_cons_self
    rw [h1] at this
    simp at this
  | a :: u₁, b :: u₂, v₁, v₂, q₁, q₂, h, h₁, h₂ => by
    simp only [List.cons_append] at h
    injection h with hab h
    obtain ⟨hu, hq, hv⟩ := state_align h (fun x hx => h₁ x (List.mem_cons_of_mem a hx))
      (fun x hx => h₂ x (List.mem_cons_of_mem b hx))
    exact ⟨by rw [hab, hu], hq, hv⟩

/-- The prefix of a configuration word carries no state letter. -/
theorem prefix_state_free (c : ConfigU A) (ls : List (ℤ × A)) :
    ∀ x ∈ TapeLetter.lft :: cellSyms c ls, x.isState = false := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · rfl
  · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
    rfl

/-- No boot letter and no halting letter occurs in a configuration word. -/
theorem boot_halt_notMem {w : List (TapeLetter A)} {c : ConfigU A}
    (h : Represents M w c) :
    TapeLetter.boot ∉ w ∧ TapeLetter.halt ∉ w := by
  obtain ⟨ls, rs, hw, -, -, -⟩ := h
  subst hw
  constructor <;>
  · intro hmem
    simp [cellSyms] at hmem

/-- The two halves of a window sit strictly below and strictly above the
head. -/
theorem window_lt {ls rs : List (ℤ × A)} {h : ℤ × A} (hlin : IsLinOrd M.Le)
    (hchain : (ls ++ h :: rs).IsChain M.SuccCell) :
    (∀ z ∈ ls, CellLt M z h) ∧ ∀ z ∈ rs, CellLt M h z := by
  have hpw := pairwise_cellLt_of_isChain hlin hchain
  rw [List.pairwise_append] at hpw
  obtain ⟨-, h2, h3⟩ := hpw
  rw [List.pairwise_cons] at h2
  exact ⟨fun z hz => h3 z hz h List.mem_cons_self, fun z hz => h2.1 z hz⟩

/-- A configuration word has exactly one state letter. -/
theorem stateCount_word (c : ConfigU A) (ls rs : List (ℤ × A)) :
    stateCount ((TapeLetter.lft :: cellSyms c ls) ++ TapeLetter.state c.state ::
      TapeLetter.sym (c.tape c.head) :: (cellSyms c rs ++ [TapeLetter.rgt])) = 1 := by
  simp [stateCount_append, stateCount_cons]

/-! ### Reading a rewriting step off a configuration word

The inversion at the heart of the backward direction: a rewriting step on a
configuration word either simulates one machine step or fires the halting
rule on the current – hence accepting – state. Each move rule carries exactly
one state letter on its left-hand side, and a configuration word carries
exactly one, so the rule can only apply at the head. -/

theorem step_inversion [Finite A] (hwf : M.WellFormed) {w w₁ : List (TapeLetter A)}
    {c : ConfigU A} (hrep : Represents M w c)
    (hstep : History.Step (MRule M) w w₁) :
    (∃ c', M.StepU c c' ∧ Represents M w₁ c') ∨ M.Acc c.state := by
  classical
  obtain ⟨hbootmem, hhaltmem⟩ := boot_halt_notMem hrep
  obtain ⟨ls, rs, hw, hchain, hposn, hblank⟩ := hrep
  obtain ⟨x, l, r, y, hrule, hu, hv⟩ := hstep
  have hwlt := window_lt hwf.1 hchain
  -- state letters count once in the whole word
  have hcnt1 : stateCount w = 1 := by rw [hw]; exact stateCount_word c ls rs
  cases hrule with
  | boot hq =>
    refine absurd ?_ hbootmem
    rw [hu]; simp
  | eraseSymL cc =>
    refine absurd ?_ hhaltmem
    rw [hu]; simp
  | eraseLft =>
    refine absurd ?_ hhaltmem
    rw [hu]; simp
  | eraseSymR cc =>
    refine absurd ?_ hhaltmem
    rw [hu]; simp
  | eraseRgt =>
    refine absurd ?_ hhaltmem
    rw [hu]; simp
  | @acc q hacc =>
    have hcnt : stateCount x = 0 ∧ stateCount y = 0 := by
      rw [hu, stateCount_append, stateCount_append] at hcnt1
      simp only [stateCount_cons, stateCount_nil, isState_state, if_true] at hcnt1
      omega
    have heq : x ++ TapeLetter.state q :: y =
        (TapeLetter.lft :: cellSyms c ls) ++ TapeLetter.state c.state ::
          (TapeLetter.sym (c.tape c.head) :: (cellSyms c rs ++ [TapeLetter.rgt])) := by
      rw [← hw, hu]; simp
    obtain ⟨-, hq', -⟩ := state_align heq (stateCount_eq_zero.mp hcnt.1)
      (prefix_state_free c ls)
    exact Or.inr (hq' ▸ hacc)
  | @moveR τ q a b q' cc hτ hR hsrc hread hdst hwrite =>
    have hcnt : stateCount x = 0 ∧ stateCount y = 0 := by
      rw [hu, stateCount_append, stateCount_append] at hcnt1
      simp only [stateCount_cons, stateCount_nil, isState_state, isState_sym,
        if_true] at hcnt1
      omega
    have heq : x ++ TapeLetter.state q :: (TapeLetter.sym a :: TapeLetter.sym cc :: y) =
        (TapeLetter.lft :: cellSyms c ls) ++ TapeLetter.state c.state ::
          (TapeLetter.sym (c.tape c.head) :: (cellSyms c rs ++ [TapeLetter.rgt])) := by
      rw [← hw, hu]; simp
    obtain ⟨hxeq, hq', hsuf⟩ := state_align heq (stateCount_eq_zero.mp hcnt.1)
      (prefix_state_free c ls)
    injection hsuf with ha hsuf
    injection ha with ha
    rcases rs with _ | ⟨r₁, rs'⟩
    · rw [cellSyms_nil, List.nil_append] at hsuf
      injection hsuf with hcon
      exact TapeLetter.absurd_of_ne hcon
    rw [cellSyms_cons, List.cons_append] at hsuf
    injection hsuf with hcc hy
    injection hcc with hcc
    have hsucc : M.SuccCell c.head r₁ := by
      have := hchain
      rw [List.isChain_split, List.isChain_cons_cons] at this
      exact this.2.1
    have hheadne : ∀ z ∈ ls, z ≠ c.head := fun z hz => (hwlt.1 z hz).ne
    have hrne : ∀ z ∈ r₁ :: rs', z ≠ c.head := fun z hz => ((hwlt.2 z hz).ne).symm
    refine Or.inl ⟨⟨q', r₁, fun z => if z = c.head then b else c.tape z⟩,
      ⟨τ, hτ, hq' ▸ hsrc, ha ▸ hread, hdst, by simpa using hwrite,
        fun z hz => if_neg hz, Or.inl ⟨hR, hsucc⟩⟩,
      ls ++ [c.head], rs', ?_, ?_, ?_, ?_⟩
    · rw [hv, hxeq, hy]
      have h1 : List.map (fun z => TapeLetter.sym (if z = c.head then b else c.tape z)) ls =
          List.map (fun z => TapeLetter.sym (c.tape z)) ls :=
        List.map_congr_left fun z hz => by rw [if_neg (hheadne z hz)]
      have h2 : List.map (fun z => TapeLetter.sym (if z = c.head then b else c.tape z)) rs' =
          List.map (fun z => TapeLetter.sym (c.tape z)) rs' :=
        List.map_congr_left fun z hz => by
          rw [if_neg (hrne z (List.mem_cons_of_mem r₁ hz))]
      simp only [cellSyms, List.map_append, List.map_cons, List.map_nil, h1, h2]
      simp [if_neg (hrne r₁ List.mem_cons_self), hcc]
    · simpa using hchain
    · intro z hz
      refine hposn z ?_
      simpa using hz
    · intro z p hp hnot
      have hne : (z, p) ≠ c.head := by
        intro hcon
        exact hnot (by simp [hcon])
      change M.Blank (if (z, p) = c.head then b else c.tape (z, p))
      rw [if_neg hne]
      refine hblank z p hp ?_
      intro hcon
      refine hnot ?_
      simpa using hcon
  | @moveREnd τ q a b q' bk hτ hR hsrc hread hdst hwrite hbk =>
    have hcnt : stateCount x = 0 ∧ stateCount y = 0 := by
      rw [hu, stateCount_append, stateCount_append] at hcnt1
      simp only [stateCount_cons, stateCount_nil, isState_state, isState_sym,
        isState_rgt, if_true] at hcnt1
      omega
    have heq : x ++ TapeLetter.state q :: (TapeLetter.sym a :: TapeLetter.rgt :: y) =
        (TapeLetter.lft :: cellSyms c ls) ++ TapeLetter.state c.state ::
          (TapeLetter.sym (c.tape c.head) :: (cellSyms c rs ++ [TapeLetter.rgt])) := by
      rw [← hw, hu]; simp
    obtain ⟨hxeq, hq', hsuf⟩ := state_align heq (stateCount_eq_zero.mp hcnt.1)
      (prefix_state_free c ls)
    injection hsuf with ha hsuf
    injection ha with ha
    rcases rs with _ | ⟨r₁, rs'⟩
    · rw [cellSyms_nil, List.nil_append] at hsuf
      injection hsuf with hrgt hy
      have hheadpos : M.Posn c.head.2 := hposn c.head (by simp)
      obtain ⟨n, hn⟩ := exists_succCell hwf hheadpos
      have hnlt : ∀ z ∈ ls ++ [c.head], CellLt M z n := by
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact (hwlt.1 z hz).trans hwf.1 (cellLt_of_succCell hn)
        · obtain rfl : z = c.head := by simpa using hz
          exact cellLt_of_succCell hn
      have hnnot : n ∉ ls ++ c.head :: ([] : List (ℤ × A)) := by
        intro hcon
        have : CellLt M n n := hnlt n (by simpa using hcon)
        exact this.ne rfl
      have hnblank : M.Blank (c.tape n) := by
        have := hblank n.1 n.2 (posn_of_succCell hn) (by simpa using hnnot)
        simpa using this
      have hnbk : c.tape n = bk := hwf.2.2.2.2 _ _ hnblank hbk
      have hheadne : ∀ z ∈ ls, z ≠ c.head := fun z hz => (hwlt.1 z hz).ne
      have hnne : n ≠ c.head := fun hcon => hnnot (by simp [hcon])
      refine Or.inl ⟨⟨q', n, fun z => if z = c.head then b else c.tape z⟩,
        ⟨τ, hτ, hq' ▸ hsrc, ha ▸ hread, hdst, by simpa using hwrite,
          fun z hz => if_neg hz, Or.inl ⟨hR, hn⟩⟩,
        ls ++ [c.head], [], ?_, ?_, ?_, ?_⟩
      · rw [hv, hxeq, hy]
        have h1 : List.map (fun z => TapeLetter.sym (if z = c.head then b else c.tape z)) ls =
            List.map (fun z => TapeLetter.sym (c.tape z)) ls :=
          List.map_congr_left fun z hz => by rw [if_neg (hheadne z hz)]
        simp only [cellSyms, List.map_append, List.map_cons, List.map_nil, h1]
        simp [if_neg hnne, hnbk]
      · simp only [List.append_assoc, List.singleton_append]
        rw [List.isChain_split]
        refine ⟨by simpa using hchain, ?_⟩
        rw [List.isChain_cons_cons]
        exact ⟨hn, List.isChain_singleton n⟩
      · intro z hz
        simp only [List.append_assoc, List.singleton_append, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with hz | hz | rfl
        · exact hposn z (by simp [hz])
        · exact hposn z (by simp [hz])
        · exact posn_of_succCell hn
      · intro z p hp hnot
        have hne : (z, p) ≠ c.head := by
          intro hcon
          exact hnot (by simp [hcon])
        change M.Blank (if (z, p) = c.head then b else c.tape (z, p))
        rw [if_neg hne]
        refine hblank z p hp ?_
        intro hcon
        refine hnot ?_
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcon
        rcases hcon with hcon | heq
        · simp [hcon]
        · exact absurd heq hne
    · rw [cellSyms_cons, List.cons_append] at hsuf
      injection hsuf with hcon
      exact TapeLetter.absurd_of_ne hcon
  | @moveL τ q a b q' cc hτ hR hsrc hread hdst hwrite =>
    have hcnt : stateCount x = 0 ∧ stateCount y = 0 := by
      rw [hu, stateCount_append, stateCount_append] at hcnt1
      simp only [stateCount_cons, stateCount_nil, isState_state, isState_sym,
        if_true] at hcnt1
      omega
    have heq : (x ++ [TapeLetter.sym cc]) ++
        TapeLetter.state q :: (TapeLetter.sym a :: y) =
        (TapeLetter.lft :: cellSyms c ls) ++ TapeLetter.state c.state ::
          (TapeLetter.sym (c.tape c.head) :: (cellSyms c rs ++ [TapeLetter.rgt])) := by
      rw [← hw, hu]; simp
    have hxfree : ∀ e ∈ x ++ [TapeLetter.sym cc], e.isState = false := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact stateCount_eq_zero.mp hcnt.1 e he
      · obtain rfl : e = TapeLetter.sym cc := by simpa using he
        rfl
    obtain ⟨hxeq, hq', hsuf⟩ := state_align heq hxfree (prefix_state_free c ls)
    injection hsuf with ha hy
    injection ha with ha
    rcases List.eq_nil_or_concat' ls with rfl | ⟨init, lst, rfl⟩
    · exfalso
      rw [cellSyms_nil] at hxeq
      rcases x with _ | ⟨e, x'⟩
      · simp only [List.nil_append] at hxeq
        injection hxeq with hcon
        exact TapeLetter.absurd_of_ne hcon
      · rw [List.cons_append] at hxeq
        injection hxeq with he hcon
        exact absurd hcon (by simp)
    · rw [cellSyms_append, cellSyms_cons, cellSyms_nil] at hxeq
      have hxeq' : x ++ [TapeLetter.sym cc] =
          (TapeLetter.lft :: cellSyms c init) ++ [TapeLetter.sym (c.tape lst)] := by
        rw [hxeq]; simp
      obtain ⟨hxeq'', hcc⟩ := List.append_inj' hxeq' rfl
      have hcc' : cc = c.tape lst := by
        injection hcc with hcc
        injection hcc with hcc
      have hsucc : M.SuccCell lst c.head := by
        have h' : (init ++ lst :: c.head :: rs).IsChain M.SuccCell := by
          simpa using hchain
        rw [List.isChain_split, List.isChain_cons_cons] at h'
        exact h'.2.1
      have hlstne : lst ≠ c.head := (cellLt_of_succCell hsucc).ne
      have hinitlt : ∀ z ∈ init, CellLt M z c.head := fun z hz =>
        hwlt.1 z (by simp [hz])
      have hrslt : ∀ z ∈ rs, CellLt M c.head z := hwlt.2
      refine Or.inl ⟨⟨q', lst, fun z => if z = c.head then b else c.tape z⟩,
        ⟨τ, hτ, hq' ▸ hsrc, ha ▸ hread, hdst, by simpa using hwrite,
          fun z hz => if_neg hz, Or.inr ⟨hR, hsucc⟩⟩,
        init, c.head :: rs, ?_, ?_, ?_, ?_⟩
      · rw [hv, hxeq'', hy]
        have h1 : List.map
              (fun z => TapeLetter.sym (if z = c.head then b else c.tape z)) init =
            List.map (fun z => TapeLetter.sym (c.tape z)) init :=
          List.map_congr_left fun z hz => by rw [if_neg (hinitlt z hz).ne]
        have h2 : List.map
              (fun z => TapeLetter.sym (if z = c.head then b else c.tape z)) rs =
            List.map (fun z => TapeLetter.sym (c.tape z)) rs :=
          List.map_congr_left fun z hz => by rw [if_neg (Ne.symm (hrslt z hz).ne)]
        simp only [cellSyms, List.map_cons, h1, h2]
        simp [if_neg hlstne, hcc']
      · simpa using hchain
      · intro z hz
        refine hposn z ?_
        simp only [List.mem_append, List.mem_cons] at hz ⊢
        tauto
      · intro z p hp hnot
        have hne : (z, p) ≠ c.head := by
          intro hcon
          refine hnot ?_
          simp [hcon]
        change M.Blank (if (z, p) = c.head then b else c.tape (z, p))
        rw [if_neg hne]
        refine hblank z p hp ?_
        intro hcon
        refine hnot ?_
        simp only [List.mem_append, List.mem_cons] at hcon ⊢
        tauto
  | @moveLEnd τ q a b q' bk hτ hR hsrc hread hdst hwrite hbk =>
    have hcnt : stateCount x = 0 ∧ stateCount y = 0 := by
      rw [hu, stateCount_append, stateCount_append] at hcnt1
      simp only [stateCount_cons, stateCount_nil, isState_state, isState_sym,
        isState_lft, if_true] at hcnt1
      omega
    have heq : (x ++ [TapeLetter.lft]) ++
        TapeLetter.state q :: (TapeLetter.sym a :: y) =
        (TapeLetter.lft :: cellSyms c ls) ++ TapeLetter.state c.state ::
          (TapeLetter.sym (c.tape c.head) :: (cellSyms c rs ++ [TapeLetter.rgt])) := by
      rw [← hw, hu]; simp
    have hxfree : ∀ e ∈ x ++ [TapeLetter.lft], e.isState = false := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact stateCount_eq_zero.mp hcnt.1 e he
      · obtain rfl : e = TapeLetter.lft := by simpa using he
        rfl
    obtain ⟨hxeq, hq', hsuf⟩ := state_align heq hxfree (prefix_state_free c ls)
    injection hsuf with ha hy
    injection ha with ha
    rcases List.eq_nil_or_concat' ls with rfl | ⟨init, lst, rfl⟩
    swap
    · exfalso
      rw [cellSyms_append, cellSyms_cons, cellSyms_nil] at hxeq
      have hxeq' : x ++ [TapeLetter.lft] =
          (TapeLetter.lft :: cellSyms c init) ++ [TapeLetter.sym (c.tape lst)] := by
        rw [hxeq]; simp
      obtain ⟨-, hcon⟩ := List.append_inj' hxeq' rfl
      injection hcon with hcon
      exact TapeLetter.absurd_of_ne hcon
    · rw [cellSyms_nil] at hxeq
      have hx0 : x = [] := by
        rcases x with _ | ⟨e, x'⟩
        · rfl
        · rw [List.cons_append] at hxeq
          injection hxeq with he hcon
          exact absurd hcon (by simp)
      have hheadpos : M.Posn c.head.2 := hposn c.head (by simp)
      obtain ⟨n, hn⟩ := exists_predCell hwf hheadpos
      have hnlt : ∀ z ∈ c.head :: rs, CellLt M n z := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact cellLt_of_succCell hn
        · exact (cellLt_of_succCell hn).trans hwf.1 (hwlt.2 z hz)
      have hnnot : n ∉ ([] : List (ℤ × A)) ++ c.head :: rs := by
        intro hcon
        have : CellLt M n n := hnlt n (by simpa using hcon)
        exact this.ne rfl
      have hnblank : M.Blank (c.tape n) := by
        have := hblank n.1 n.2 (posn_of_succCell_left hn) (by simpa using hnnot)
        simpa using this
      have hnbk : c.tape n = bk := hwf.2.2.2.2 _ _ hnblank hbk
      have hnne : n ≠ c.head := (cellLt_of_succCell hn).ne
      have hrslt : ∀ z ∈ rs, CellLt M c.head z := hwlt.2
      refine Or.inl ⟨⟨q', n, fun z => if z = c.head then b else c.tape z⟩,
        ⟨τ, hτ, hq' ▸ hsrc, ha ▸ hread, hdst, by simpa using hwrite,
          fun z hz => if_neg hz, Or.inr ⟨hR, hn⟩⟩,
        [], c.head :: rs, ?_, ?_, ?_, ?_⟩
      · rw [hv, hx0, hy]
        have h2 : List.map (fun z => TapeLetter.sym (if z = c.head then b else c.tape z)) rs =
            List.map (fun z => TapeLetter.sym (c.tape z)) rs :=
          List.map_congr_left fun z hz => by rw [if_neg (Ne.symm (hrslt z hz).ne)]
        simp only [cellSyms, List.map_cons, List.map_nil, h2]
        simp [if_neg hnne, hnbk]
      · rw [List.nil_append, List.isChain_cons_cons]
        exact ⟨hn, by simpa using hchain⟩
      · intro z hz
        simp only [List.nil_append, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact posn_of_succCell_left hn
        · exact hposn z (by simpa using hz)
      · intro z p hp hnot
        have hne : (z, p) ≠ c.head := by
          intro hcon
          refine hnot ?_
          simp [hcon]
        change M.Blank (if (z, p) = c.head then b else c.tape (z, p))
        rw [if_neg hne]
        refine hblank z p hp ?_
        intro hcon
        refine hnot ?_
        simp only [List.nil_append, List.mem_cons] at hcon ⊢
        tauto

/-! ### Writing a machine step as a rewriting step

The forward direction: one machine step is one rewriting step – the boundary
variants of the moves extend the window in the same stroke, so no separate
padding step is ever needed. -/

theorem exists_step_of_stepU [Finite A] (hwf : M.WellFormed) {w : List (TapeLetter A)}
    {c c' : ConfigU A} (hrep : Represents M w c) (h : M.StepU c c') :
    ∃ w', History.Step (MRule M) w w' ∧ Represents M w' c' := by
  classical
  obtain ⟨ls, rs, hw, hchain, hposn, hblank⟩ := hrep
  obtain ⟨τ, hτ, hsrc, hread, hdst, hwrite, hframe, hmove⟩ := h
  have hwlt := window_lt hwf.1 hchain
  have hlsne : ∀ z ∈ ls, z ≠ c.head := fun z hz => (hwlt.1 z hz).ne
  have hcls : cellSyms c' ls = cellSyms c ls :=
    cellSyms_congr fun z hz => hframe z (hlsne z hz)
  rcases hmove with ⟨hR, hmv⟩ | ⟨hR, hmv⟩
  · -- a right move
    have hne' : c'.head ≠ c.head := Ne.symm (cellLt_of_succCell hmv).ne
    rcases rs with _ | ⟨r₁, rs'⟩
    · -- at the right edge: the head's next cell enters the window, blank
      have hlt : ∀ z ∈ ls ++ [c.head], CellLt M z c'.head := by
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact (hwlt.1 z hz).trans hwf.1 (cellLt_of_succCell hmv)
        · obtain rfl : z = c.head := by simpa using hz
          exact cellLt_of_succCell hmv
      have hnnot : c'.head ∉ ls ++ [c.head] := fun hcon => (hlt _ hcon).ne rfl
      have hnblank : M.Blank (c.tape c'.head) := by
        have := hblank c'.head.1 c'.head.2 (posn_of_succCell hmv) (by simpa using hnnot)
        simpa using this
      have htn : c'.tape c'.head = c.tape c'.head := hframe _ hne'
      refine ⟨(TapeLetter.lft :: cellSyms c ls) ++
          [TapeLetter.sym (c'.tape c.head), TapeLetter.state c'.state,
            TapeLetter.sym (c.tape c'.head), TapeLetter.rgt] ++ [],
        ⟨TapeLetter.lft :: cellSyms c ls,
          [TapeLetter.state c.state, TapeLetter.sym (c.tape c.head), TapeLetter.rgt], _, [],
          MRule.moveREnd hτ hR hsrc hread hdst hwrite (htn ▸ hnblank), by rw [hw]; simp, rfl⟩,
        ls ++ [c.head], [], ?_, ?_, ?_, ?_⟩
      · simp [hcls, htn]
      · simp only [List.append_assoc, List.singleton_append]
        rw [List.isChain_split]
        refine ⟨by simpa using hchain, ?_⟩
        rw [List.isChain_cons_cons]
        exact ⟨hmv, List.isChain_singleton _⟩
      · intro z hz
        simp only [List.append_assoc, List.singleton_append,
          List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with hz | hz | rfl
        · exact hposn z (by simp [hz])
        · exact hposn z (by simp [hz])
        · exact posn_of_succCell hmv
      · intro z p hp hnot
        have hne : (z, p) ≠ c.head := by
          intro hcon
          exact hnot (by simp [hcon])
        rw [hframe _ hne]
        refine hblank z p hp ?_
        intro hcon
        refine hnot ?_
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcon ⊢
        tauto
    · -- inside the window: the next cell is already there
      have hsucc : M.SuccCell c.head r₁ := by
        have := hchain
        rw [List.isChain_split, List.isChain_cons_cons] at this
        exact this.2.1
      have hr1 : c'.head = r₁ := succCell_right_unique hwf hmv hsucc
      have hr1ne : r₁ ≠ c.head := Ne.symm (cellLt_of_succCell hsucc).ne
      have hrsne : ∀ z ∈ rs', z ≠ c.head := fun z hz =>
        Ne.symm (hwlt.2 z (List.mem_cons_of_mem r₁ hz)).ne
      have hcrs : cellSyms c' rs' = cellSyms c rs' :=
        cellSyms_congr fun z hz => hframe z (hrsne z hz)
      refine ⟨(TapeLetter.lft :: cellSyms c ls) ++
          [TapeLetter.sym (c'.tape c.head), TapeLetter.state c'.state,
            TapeLetter.sym (c.tape r₁)] ++ (cellSyms c rs' ++ [TapeLetter.rgt]),
        ⟨TapeLetter.lft :: cellSyms c ls,
          [TapeLetter.state c.state, TapeLetter.sym (c.tape c.head), TapeLetter.sym (c.tape r₁)],
          _, cellSyms c rs' ++ [TapeLetter.rgt],
          MRule.moveR hτ hR hsrc hread hdst hwrite, by rw [hw]; simp, rfl⟩,
        ls ++ [c.head], rs', ?_, ?_, ?_, ?_⟩
      · rw [hr1]
        simp [hcls, hcrs, hframe r₁ hr1ne]
      · rw [hr1]
        simpa using hchain
      · intro z hz
        rw [hr1] at hz
        refine hposn z ?_
        simpa using hz
      · intro z p hp hnot
        rw [hr1] at hnot
        have hne : (z, p) ≠ c.head := by
          intro hcon
          exact hnot (by simp [hcon])
        rw [hframe _ hne]
        refine hblank z p hp ?_
        intro hcon
        refine hnot ?_
        simpa using hcon
  · -- a left move
    have hne' : c'.head ≠ c.head := (cellLt_of_succCell hmv).ne
    have hrsne : ∀ z ∈ rs, z ≠ c.head := fun z hz => Ne.symm (hwlt.2 z hz).ne
    have hcrs : cellSyms c' rs = cellSyms c rs :=
      cellSyms_congr fun z hz => hframe z (hrsne z hz)
    rcases List.eq_nil_or_concat' ls with rfl | ⟨init, lst, rfl⟩
    · -- at the left edge: the head's previous cell enters the window, blank
      have hlt : ∀ z ∈ c.head :: rs, CellLt M c'.head z := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact cellLt_of_succCell hmv
        · exact (cellLt_of_succCell hmv).trans hwf.1 (hwlt.2 z hz)
      have hnnot : c'.head ∉ ([] : List (ℤ × A)) ++ c.head :: rs :=
        fun hcon => (hlt _ (by simpa using hcon)).ne rfl
      have hnblank : M.Blank (c.tape c'.head) := by
        have := hblank c'.head.1 c'.head.2 (posn_of_succCell_left hmv)
          (by simpa using hnnot)
        simpa using this
      have htn : c'.tape c'.head = c.tape c'.head := hframe _ hne'
      refine ⟨[] ++ [TapeLetter.lft, TapeLetter.state c'.state,
            TapeLetter.sym (c.tape c'.head), TapeLetter.sym (c'.tape c.head)] ++
            (cellSyms c rs ++ [TapeLetter.rgt]),
        ⟨[], [TapeLetter.lft, TapeLetter.state c.state, TapeLetter.sym (c.tape c.head)],
          _, cellSyms c rs ++ [TapeLetter.rgt],
          MRule.moveLEnd hτ hR hsrc hread hdst hwrite (htn ▸ hnblank), by rw [hw]; simp, rfl⟩,
        [], c.head :: rs, ?_, ?_, ?_, ?_⟩
      · simp [hcrs, htn]
      · rw [List.nil_append, List.isChain_cons_cons]
        exact ⟨hmv, by simpa using hchain⟩
      · intro z hz
        simp only [List.nil_append, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact posn_of_succCell_left hmv
        · exact hposn z (by simpa using hz)
      · intro z p hp hnot
        have hne : (z, p) ≠ c.head := by
          intro hcon
          refine hnot ?_
          simp [hcon]
        rw [hframe _ hne]
        refine hblank z p hp ?_
        intro hcon
        refine hnot ?_
        simp only [List.nil_append, List.mem_cons] at hcon ⊢
        tauto
    · -- inside the window: the previous cell is already there
      have hsucc : M.SuccCell lst c.head := by
        have h' : (init ++ lst :: c.head :: rs).IsChain M.SuccCell := by
          simpa using hchain
        rw [List.isChain_split, List.isChain_cons_cons] at h'
        exact h'.2.1
      have hlst : c'.head = lst := succCell_left_unique hwf hmv hsucc
      have hlstne : lst ≠ c.head := (cellLt_of_succCell hsucc).ne
      have hinitne : ∀ z ∈ init, z ≠ c.head := fun z hz => hlsne z (by simp [hz])
      have hcinit : cellSyms c' init = cellSyms c init :=
        cellSyms_congr fun z hz => hframe z (hinitne z hz)
      refine ⟨(TapeLetter.lft :: cellSyms c init) ++
          [TapeLetter.state c'.state, TapeLetter.sym (c.tape lst),
            TapeLetter.sym (c'.tape c.head)] ++ (cellSyms c rs ++ [TapeLetter.rgt]),
        ⟨TapeLetter.lft :: cellSyms c init,
          [TapeLetter.sym (c.tape lst), TapeLetter.state c.state,
            TapeLetter.sym (c.tape c.head)],
          _, cellSyms c rs ++ [TapeLetter.rgt],
          MRule.moveL hτ hR hsrc hread hdst hwrite, by rw [hw]; simp [cellSyms_append], rfl⟩,
        init, c.head :: rs, ?_, ?_, ?_, ?_⟩
      · rw [hlst]
        simp [hcinit, hcrs, hframe lst hlstne]
      · rw [hlst]
        simpa using hchain
      · intro z hz
        rw [hlst] at hz
        refine hposn z ?_
        simp only [List.mem_append, List.mem_cons] at hz ⊢
        tauto
      · intro z p hp hnot
        rw [hlst] at hnot
        have hne : (z, p) ≠ c.head := by
          intro hcon
          refine hnot ?_
          simp [hcon]
        rw [hframe _ hne]
        refine hblank z p hp ?_
        intro hcon
        refine hnot ?_
        simp only [List.mem_append, List.mem_cons] at hcon ⊢
        tauto

/-! ### Whole runs, and the halting phase -/

/-- A run of the machine is a derivation between words of its endpoints. -/
theorem derives_of_run [Finite A] (hwf : M.WellFormed) :
    ∀ {n : ℕ} {c c' : ConfigU A}, M.StepsInU n c c' →
      ∀ {w}, Represents M w c →
        ∃ w', History.Derives (MRule M) w w' ∧ Represents M w' c'
  | 0, c, c', h, w, hrep => ⟨w, Relation.ReflTransGen.refl, (show c = c' from h) ▸ hrep⟩
  | n + 1, c, c', h, w, hrep => by
    obtain ⟨d, hstep, hrest⟩ := h
    obtain ⟨w₁, h1, hrep₁⟩ := exists_step_of_stepU hwf hrep hstep
    obtain ⟨w', hd, hrep'⟩ := derives_of_run hwf hrest hrep₁
    exact ⟨w', Relation.ReflTransGen.head h1 hd, hrep'⟩

/-- The halting letter melts a block of symbols to its left away. -/
theorem derives_eraseL (u : List A) :
    History.Derives (MRule M) (u.map TapeLetter.sym ++ [TapeLetter.halt])
      [TapeLetter.halt] := by
  induction u with
  | nil => exact Relation.ReflTransGen.refl
  | cons a u ih =>
    refine Relation.ReflTransGen.trans ?_
      (Relation.ReflTransGen.single
        (⟨[], [TapeLetter.sym a, TapeLetter.halt], [TapeLetter.halt], [],
          MRule.eraseSymL a, by simp, by simp⟩ :
          History.Step (MRule M) [TapeLetter.sym a, TapeLetter.halt] [TapeLetter.halt]))
    have := ih.congr [TapeLetter.sym a] []
    simpa using this

/-- The halting letter melts a block of symbols to its right away. -/
theorem derives_eraseR (u : List A) :
    History.Derives (MRule M) (TapeLetter.halt :: u.map TapeLetter.sym)
      [TapeLetter.halt] := by
  induction u with
  | nil => exact Relation.ReflTransGen.refl
  | cons a u ih =>
    refine Relation.ReflTransGen.head
      (⟨[], [TapeLetter.halt, TapeLetter.sym a], [TapeLetter.halt], u.map TapeLetter.sym,
        MRule.eraseSymR a, by simp, by simp⟩ :
        History.Step (MRule M) _ (TapeLetter.halt :: u.map TapeLetter.sym)) ih

/-- **From an accepting configuration the derivation closes**: the state
letter becomes the halting letter, which then swallows the whole word. -/
theorem derives_halt_of_acc {w : List (TapeLetter A)} {c : ConfigU A}
    (hrep : Represents M w c) (hacc : M.Acc c.state) :
    History.Derives (MRule M) w [TapeLetter.halt] := by
  obtain ⟨ls, rs, hw, -, -, -⟩ := hrep
  -- the state letter becomes the halting letter
  have h1 : History.Step (MRule M) w
      ((TapeLetter.lft :: cellSyms c ls) ++ TapeLetter.halt ::
        (TapeLetter.sym (c.tape c.head) :: (cellSyms c rs ++ [TapeLetter.rgt]))) :=
    ⟨TapeLetter.lft :: cellSyms c ls, [TapeLetter.state c.state], [TapeLetter.halt],
      TapeLetter.sym (c.tape c.head) :: (cellSyms c rs ++ [TapeLetter.rgt]),
      MRule.acc hacc, by rw [hw]; simp, by simp⟩
  -- the halting letter swallows the left half of the window
  have h2 : History.Derives (MRule M)
      ((TapeLetter.lft :: cellSyms c ls) ++ TapeLetter.halt ::
        (TapeLetter.sym (c.tape c.head) :: (cellSyms c rs ++ [TapeLetter.rgt])))
      ([TapeLetter.lft, TapeLetter.halt] ++
        (TapeLetter.sym (c.tape c.head) :: (cellSyms c rs ++ [TapeLetter.rgt]))) := by
    have h := (derives_eraseL (M := M) (ls.map c.tape)).congr [TapeLetter.lft]
      (TapeLetter.sym (c.tape c.head) :: (cellSyms c rs ++ [TapeLetter.rgt]))
    have hsyms : (ls.map c.tape).map TapeLetter.sym = cellSyms c ls := by
      simp [cellSyms, List.map_map, Function.comp_def]
    rw [hsyms] at h
    simpa using h
  -- then the left endmarker
  have h3 : History.Step (MRule M)
      ([TapeLetter.lft, TapeLetter.halt] ++
        (TapeLetter.sym (c.tape c.head) :: (cellSyms c rs ++ [TapeLetter.rgt])))
      (TapeLetter.halt :: (TapeLetter.sym (c.tape c.head) ::
        (cellSyms c rs ++ [TapeLetter.rgt]))) :=
    ⟨[], [TapeLetter.lft, TapeLetter.halt], [TapeLetter.halt],
      TapeLetter.sym (c.tape c.head) :: (cellSyms c rs ++ [TapeLetter.rgt]),
      MRule.eraseLft, by simp, by simp⟩
  -- then the right half of the window
  have h4 : History.Derives (MRule M)
      (TapeLetter.halt :: (TapeLetter.sym (c.tape c.head) ::
        (cellSyms c rs ++ [TapeLetter.rgt])))
      [TapeLetter.halt, TapeLetter.rgt] := by
    have h := (derives_eraseR (M := M) (c.tape c.head :: rs.map c.tape)).congr []
      [TapeLetter.rgt]
    have hsyms : (c.tape c.head :: rs.map c.tape).map TapeLetter.sym =
        TapeLetter.sym (c.tape c.head) :: cellSyms c rs := by
      simp [cellSyms, List.map_map, Function.comp_def]
    rw [hsyms] at h
    simpa using h
  -- and finally the right endmarker
  have h5 : History.Step (MRule M) [TapeLetter.halt, TapeLetter.rgt] [TapeLetter.halt] :=
    ⟨[], [TapeLetter.halt, TapeLetter.rgt], [TapeLetter.halt], [],
      MRule.eraseRgt, by simp, by simp⟩
  exact (((Relation.ReflTransGen.head h1 h2).tail h3).trans h4).tail h5

/-! ### The start word

The start word writes the input page between the endmarkers, with the boot
letter in the state slot; the boot rule turns it into a word of an initial
configuration. The page is read along an enumeration of the positions in the
machine's order. -/

variable (M) in
/-- `ps` enumerates the positions, in the machine's order. -/
def IsPosEnum (ps : List A) : Prop :=
  ps.Pairwise (fun p q => M.Le p q ∧ p ≠ q) ∧ ∀ p, p ∈ ps ↔ M.Posn p

/-- The start word of an input page: endmarkers, the boot letter, and the
symbols of the page. -/
def startWord (inp : List A) : List (TapeLetter A) :=
  TapeLetter.lft :: TapeLetter.boot :: (inp.map TapeLetter.sym ++ [TapeLetter.rgt])

/-- A machine with a position has a nonempty enumeration. -/
theorem IsPosEnum.ne_nil (hwf : M.WellFormed) {ps : List A} (hps : IsPosEnum M ps) :
    ps ≠ [] := by
  obtain ⟨p, hp⟩ := hwf.2.1
  intro h
  rw [h] at hps
  exact absurd ((hps.2 p).mpr hp) (by simp)

/-- Consecutive entries of an enumeration are consecutive positions. -/
theorem IsPosEnum.isChain (hlin : IsLinOrd M.Le) {ps : List A} (hps : IsPosEnum M ps) :
    ps.IsChain (SuccPos M.Le M.Posn) := by
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro p q l₁ l₂ heq
  have hpw := heq ▸ hps.1
  rw [List.pairwise_append] at hpw
  obtain ⟨-, hpw2, hcross⟩ := hpw
  rw [List.pairwise_cons] at hpw2
  obtain ⟨hpq', hpw3⟩ := hpw2
  rw [List.pairwise_cons] at hpw3
  have hpq := hpq' q List.mem_cons_self
  refine ⟨(hps.2 p).mp (heq ▸ (by simp)), (hps.2 q).mp (heq ▸ (by simp)),
    hpq.1, hpq.2, fun r hr hpr hrq => ?_⟩
  have hrps : r ∈ ps := (hps.2 r).mpr hr
  rw [heq] at hrps
  rcases List.mem_append.mp hrps with hr1 | hr2
  · have h := hcross r hr1 p List.mem_cons_self
    exact absurd (hlin.2.2.1 r p h.1 hpr) h.2
  · rcases List.mem_cons.mp hr2 with rfl | hr3
    · exact Or.inl rfl
    rcases List.mem_cons.mp hr3 with rfl | hr4
    · exact Or.inr rfl
    · have h := hpw3.1 r hr4
      exact absurd (hlin.2.2.1 q r h.1 hrq) h.2

/-- The first entry of an enumeration is the lowest position. -/
theorem IsPosEnum.head_minPos (hlin : IsLinOrd M.Le) {p : A} {pr : List A}
    (hps : IsPosEnum M (p :: pr)) : MinPos M.Le M.Posn p := by
  refine ⟨(hps.2 p).mp (by simp), fun q hq => ?_⟩
  rcases List.mem_cons.mp ((hps.2 q).mpr hq) with rfl | hq'
  · exact hlin.1 q
  · exact ((List.pairwise_cons.mp hps.1).1 q hq').1

/-- **A well-formed machine with a start state has an initial configuration on
the unbounded tape**, its input page filled by choice and the rest blank. -/
theorem exists_isInitU [Finite A] (hwf : M.WellFormed) {q₀ : A} (hq : M.Start q₀) :
    ∃ c₀ : ConfigU A, M.IsInitU c₀ ∧ c₀.state = q₀ := by
  classical
  obtain ⟨p₀, hp₀⟩ := exists_minPos hwf.1 hwf.2.1
  obtain ⟨b₀, hb₀⟩ := hwf.2.2.2.1
  refine ⟨⟨q₀, (0, p₀),
    fun x => if h : x.1 = 0 ∧ ∃ a, M.Inp x.2 a then h.2.choose else b₀⟩,
    ⟨hq, rfl, hp₀, fun z p hp => ⟨fun hz => ?_, fun hz => ?_⟩⟩, rfl⟩
  · by_cases h : ∃ a, M.Inp p a
    · exact Or.inl (by simpa only [dif_pos (⟨hz, h⟩ : (z = 0) ∧ _)] using
        (⟨hz, h⟩ : (z = 0) ∧ ∃ a, M.Inp p a).2.choose_spec)
    · refine Or.inr ⟨fun b hb => h ⟨b, hb⟩, ?_⟩
      simpa only [dif_neg (fun hcon : (z = 0) ∧ ∃ a, M.Inp p a => h hcon.2)] using hb₀
  · simpa only [dif_neg (fun hcon : (z = 0) ∧ ∃ a, M.Inp p a => hz hcon.1)] using hb₀

/-- **The word of an initial configuration**: the input page between the
endmarkers, the state in front of its first cell. -/
theorem represents_of_isInitU [Finite A] (hwf : M.WellFormed) {ps inp : List A}
    (hps : IsPosEnum M ps) (hinp : List.Forall₂ M.InitTape ps inp)
    {c₀ : ConfigU A} (hinit : M.IsInitU c₀) :
    Represents M (TapeLetter.lft :: TapeLetter.state c₀.state ::
      (inp.map TapeLetter.sym ++ [TapeLetter.rgt])) c₀ := by
  obtain ⟨hstart, hz0, hmin, htape⟩ := hinit
  -- the letters of the page are the cells' contents
  have hcells : ∀ (ps' inp' : List A), List.Forall₂ M.InitTape ps' inp' →
      (∀ p ∈ ps', M.Posn p) →
      cellSyms c₀ (ps'.map fun p => ((0 : ℤ), p)) = inp'.map TapeLetter.sym := by
    intro ps' inp' hf
    induction hf with
    | nil => intro; rfl
    | @cons p a ps'' inp'' hpa hf ih =>
      intro hpos
      have hp : M.Posn p := hpos p (by simp)
      have : c₀.tape (0, p) = a :=
        TMData.initTape_functional hwf ((htape 0 p hp).1 rfl) hpa
      simp only [List.map_cons, cellSyms_cons, this]
      rw [ih fun q hq => hpos q (by simp [hq])]
  rcases ps with _ | ⟨p₁, pr⟩
  · exact absurd rfl (hps.ne_nil hwf)
  rcases List.forall₂_cons_left_iff.mp hinp with ⟨a₁, ar, hpa₁, har, rfl⟩
  have hposn : ∀ p ∈ p₁ :: pr, M.Posn p := fun p hp => (hps.2 p).mp hp
  have hhead : c₀.head = ((0 : ℤ), p₁) :=
    Prod.ext hz0 (minPos_unique hwf.1 hmin (hps.head_minPos hwf.1))
  have hchain : ((p₁ :: pr).map fun p => ((0 : ℤ), p)).IsChain M.SuccCell := by
    rw [List.isChain_map]
    exact (hps.isChain hwf.1).imp fun a b hp => Or.inl ⟨rfl, hp⟩
  have hca := hcells (p₁ :: pr) (a₁ :: ar) hinp hposn
  simp only [List.map_cons, cellSyms_cons] at hca
  injection hca with hca₁ hcar
  injection hca₁ with hca₁
  refine ⟨[], pr.map fun p => ((0 : ℤ), p), ?_, ?_, ?_, ?_⟩
  · rw [hhead, hca₁, hcar]
    simp
  · rw [List.nil_append, hhead]
    simpa using hchain
  · intro x hx
    rw [List.nil_append, hhead] at hx
    have : x ∈ (p₁ :: pr).map fun p => ((0 : ℤ), p) := by simpa using hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp this
    exact hposn p hp
  · intro z p hp hnot
    rw [List.nil_append, hhead] at hnot
    rcases eq_or_ne z 0 with rfl | hz
    · exfalso
      refine hnot ?_
      have hmem : p ∈ p₁ :: pr := (hps.2 p).mpr hp
      exact List.mem_map.mpr ⟨p, hmem, rfl⟩
    · exact (htape z p hp).2 hz

/-- No letter of a start word is a state or halting letter, and its only boot
letter is the one in the state slot. -/
theorem stateCount_startWord (inp : List A) : stateCount (startWord inp) = 0 := by
  rw [stateCount_eq_zero]
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · rfl
  rcases List.mem_cons.mp hx with rfl | hx
  · rfl
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
    rfl
  · obtain rfl : x = TapeLetter.rgt := by simpa using hx
    rfl

/-! ### The equivalence -/

/-- The backward reading: a derivation from a configuration word to the
halting word yields an accepting run from that configuration. -/
theorem acceptsU_of_derives [Finite A] (hwf : M.WellFormed) {w : List (TapeLetter A)}
    (hder : History.Derives (MRule M) w [TapeLetter.halt]) :
    ∀ c : ConfigU A, Represents M w c →
      ∃ (c' : ConfigU A) (n : ℕ), M.StepsInU n c c' ∧ M.Acc c'.state := by
  induction hder using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro c hrep
    exfalso
    obtain ⟨ls, rs, hw, -, -, -⟩ := hrep
    rw [List.cons_append] at hw
    injection hw with hcon
    exact TapeLetter.absurd_of_ne hcon
  | @head w' w₁ hstep hrest ih =>
    intro c hrep
    rcases step_inversion hwf hrep hstep with ⟨c', hstepU, hrep'⟩ | hacc
    · obtain ⟨c'', n, hrun, hacc⟩ := ih c' hrep'
      exact ⟨c'', n + 1, ⟨c', hstepU, hrun⟩, hacc⟩
    · exact ⟨c, 0, rfl, hacc⟩

/-- **Acceptance is derivability**: the machine accepts exactly when the
rewriting system derives the halting word from the start word. -/
theorem acceptsU_iff_derives [Finite A] (hwf : M.WellFormed) {ps inp : List A}
    (hps : IsPosEnum M ps) (hinp : List.Forall₂ M.InitTape ps inp) :
    M.AcceptsU ↔ History.Derives (MRule M) (startWord inp) [TapeLetter.halt] := by
  constructor
  · rintro ⟨c₀, c, n, hinit, hrun, hacc⟩
    have hboot : History.Step (MRule M) (startWord inp)
        (TapeLetter.lft :: TapeLetter.state c₀.state ::
          (inp.map TapeLetter.sym ++ [TapeLetter.rgt])) :=
      ⟨[TapeLetter.lft], [TapeLetter.boot], [TapeLetter.state c₀.state],
        inp.map TapeLetter.sym ++ [TapeLetter.rgt], MRule.boot hinit.1,
        by simp [startWord], by simp⟩
    have hrep₀ := represents_of_isInitU hwf hps hinp hinit
    obtain ⟨w', hd, hrep'⟩ := derives_of_run hwf hrun hrep₀
    exact Relation.ReflTransGen.head hboot (hd.trans (derives_halt_of_acc hrep' hacc))
  · intro hder
    -- the first step of the derivation can only be the boot rule
    rcases Relation.ReflTransGen.cases_head hder with heq | ⟨w₁, hstep, hrest⟩
    · exfalso
      rw [startWord] at heq
      injection heq with hcon
      exact TapeLetter.absurd_of_ne hcon
    obtain ⟨x, l, r, y, hrule, hu, hv⟩ := hstep
    have hcnt0 : stateCount (startWord inp) = 0 := stateCount_startWord inp
    have hhaltnot : TapeLetter.halt ∉ startWord inp := by
      simp [startWord]
    cases hrule with
    | moveR hτ hR hsrc hread hdst hwrite =>
      rw [hu, stateCount_append, stateCount_append] at hcnt0
      simp [stateCount_cons] at hcnt0
    | moveREnd hτ hR hsrc hread hdst hwrite hbk =>
      rw [hu, stateCount_append, stateCount_append] at hcnt0
      simp [stateCount_cons] at hcnt0
    | moveL hτ hR hsrc hread hdst hwrite =>
      rw [hu, stateCount_append, stateCount_append] at hcnt0
      simp [stateCount_cons] at hcnt0
    | moveLEnd hτ hR hsrc hread hdst hwrite hbk =>
      rw [hu, stateCount_append, stateCount_append] at hcnt0
      simp [stateCount_cons] at hcnt0
    | acc hacc =>
      rw [hu, stateCount_append, stateCount_append] at hcnt0
      simp [stateCount_cons] at hcnt0
    | eraseSymL cc => exact absurd (by rw [hu]; simp) hhaltnot
    | eraseLft => exact absurd (by rw [hu]; simp) hhaltnot
    | eraseSymR cc => exact absurd (by rw [hu]; simp) hhaltnot
    | eraseRgt => exact absurd (by rw [hu]; simp) hhaltnot
    | @boot q₀ hq₀ =>
      -- align the boot letter: the prefix can only be the left endmarker
      have hx : x = [TapeLetter.lft] ∧ y = inp.map TapeLetter.sym ++ [TapeLetter.rgt] := by
        have hbootnot : TapeLetter.boot ∉ inp.map TapeLetter.sym ++ [TapeLetter.rgt] := by
          simp
        rcases x with _ | ⟨e, x'⟩
        · exfalso
          rw [startWord] at hu
          simp only [List.nil_append, List.cons_append] at hu
          injection hu with hcon
          exact TapeLetter.absurd_of_ne hcon
        rcases x' with _ | ⟨e', x''⟩
        · rw [startWord] at hu
          simp only [List.cons_append, List.nil_append] at hu
          injection hu with he hu
          injection hu with hb hu
          exact ⟨by rw [he], hu.symm⟩
        · exfalso
          rw [startWord] at hu
          simp only [List.cons_append] at hu
          injection hu with he hu
          injection hu with he' hu
          refine hbootnot ?_
          rw [hu]
          simp
      obtain ⟨rfl, rfl⟩ := hx
      obtain ⟨c₀, hinit, hst⟩ := exists_isInitU hwf hq₀
      have hrep₀ := represents_of_isInitU hwf hps hinp hinit
      rw [hst] at hrep₀
      have hw₁ : w₁ = TapeLetter.lft :: TapeLetter.state q₀ ::
          (inp.map TapeLetter.sym ++ [TapeLetter.rgt]) := by
        rw [hv]; simp
      obtain ⟨c', n, hrun, hacc⟩ :=
        acceptsU_of_derives hwf (hw₁ ▸ hrest) c₀ hrep₀
      exact ⟨c₀, c', n, hinit, hrun, hacc⟩

/-- **Acceptance is having a match**: the domino system of the machine's
rewriting rules has a match exactly when the machine accepts. -/
theorem acceptsU_iff_hasMatch [Finite A] (hwf : M.WellFormed) {ps inp : List A}
    (hps : IsPosEnum M ps) (hinp : List.Forall₂ M.InitTape ps inp) :
    M.AcceptsU ↔
      History.HasMatch (MRule M) (startWord inp) TapeLetter.halt :=
  (acceptsU_iff_derives hwf hps hinp).trans
    (History.hasMatch_iff (fun _ _ h => mRule_ne h) (startWord inp) TapeLetter.halt).symm

end HaltPcp

end DescriptiveComplexity
