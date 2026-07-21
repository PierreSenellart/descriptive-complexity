/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import FOReduction.OccurrenceOrder

/-!
# The 3-coloring gadget graph of a CNF structure

Combinatorial core of the reduction from SAT to 3-colorability: the classical
gadget graph associated to a CNF, and the proof that it is 3-colorable iff the
CNF is satisfiable. The first-order definition of this graph (as a tagged
2-dimensional interpretation) is in
`FOReduction.Problems.ThreeColorability.FromSat`; here everything is purely
semantic.

Vertices are tagged pairs `(t, a, b)` with `t : SatTag` and `a b` elements of
the CNF structure:

* `palT`/`palF`/`palB`: the palette ("true"/"false"/"base"). All copies of one
  palette tag form one color class: every copy of one tag is adjacent to every
  copy of every other tag, so in a proper coloring all `palT` copies share a
  color, etc. This avoids singling out canonical elements.
* `lit s` at `(x, x)`: the literal vertex for `x` with sign `s`; adjacent to
  its complementary literal and to the base palette, so it is colored
  true-or-false, consistently with the complementary literal.
* `gu s`/`gv s`/`go s` at `(c, x)`: the OR-gate for the non-first occurrence
  `(x, s)` of the clause `c`: a triangle whose inputs `gu`, `gv` are adjacent
  respectively to the previous prefix node (the literal vertex of the first
  occurrence, or the previous gate output `go`) and to the literal vertex of
  `(x, s)`. The gate output `go` can be colored "true" iff some input is; the
  output of the last gate is forced true by edges to `palF` and `palB`.
* a clause whose unique literal is `(x, s)` forces its literal directly:
  `lit s` at `(x, x)` is adjacent to `palF` (as well as `palB`);
* `spoil` at `(c, c)`: adjacent to all three palette classes when `c` is an
  empty clause, making the graph non-3-colorable, as required.

Junk vertices (tuples not matching the shapes above) have no incident edges.

The main result is `FirstOrder.SatToCol.satisfiable_iff_gadColoring`.
-/

namespace FirstOrder

namespace SatToCol

open Language Structure SatOcc

/-- Tags of the gadget graph. -/
inductive SatTag : Type
  /-- Palette "true". -/
  | palT
  /-- Palette "false". -/
  | palF
  /-- Palette "base". -/
  | palB
  /-- Literal vertex, at diagonal pairs `(x, x)`. -/
  | lit (s : Bool)
  /-- OR-gate input from the previous prefix node, at pairs `(c, x)`. -/
  | gu (s : Bool)
  /-- OR-gate input from the literal vertex, at pairs `(c, x)`. -/
  | gv (s : Bool)
  /-- OR-gate output, at pairs `(c, x)`. -/
  | go (s : Bool)
  /-- Spoiler for empty clauses, at diagonal pairs `(c, c)`. -/
  | spoil
  deriving DecidableEq, Fintype

/-- Everything in `Fin 3` is one of three pairwise distinct values. -/
private theorem fin3_cases : ∀ z a b c : Fin 3, a ≠ b → b ≠ c → c ≠ a →
    z = a ∨ z = b ∨ z = c := by decide

/-- The 3-coloring forcing pattern of an OR-gate: if both inputs avoid `f` and
each other, the output is forced to `f`. -/
private theorem fin3_forced : ∀ t f b u v o : Fin 3, t ≠ f → f ≠ b → b ≠ t →
    u ≠ f → v ≠ f → u ≠ v → o ≠ u → o ≠ v → o = f := by decide

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

/-- One direction of the edge relation of the gadget graph, in component form:
`Core t₁ a₁ b₁ t₂ a₂ b₂` relates the vertex `(t₁, (a₁, b₁))` to
`(t₂, (a₂, b₂))`. The edge relation of the graph is its symmetrization. -/
def Core : SatTag → A → A → SatTag → A → A → Prop
  | .palT, _, _, .palF, _, _ => True
  | .palF, _, _, .palB, _, _ => True
  | .palB, _, _, .palT, _, _ => True
  | .lit s, a₁, b₁, .lit t, a₂, b₂ => t = !s ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₁ = a₂
  | .lit _, a₁, b₁, .palB, _, _ => a₁ = b₁
  | .lit s, a₁, b₁, .palF, _, _ => a₁ = b₁ ∧ ∃ c, MinOcc c a₁ s ∧ MaxOcc c a₁ s
  | .gv s, c, x, .lit t, a₂, b₂ => t = s ∧ a₂ = b₂ ∧ a₂ = x ∧ Chained c x s
  | .gu s, c, x, .lit t, a₂, b₂ =>
      a₂ = b₂ ∧ Chained c x s ∧ MinOcc c a₂ t ∧ SuccOcc c a₂ t x s
  | .gu s, c, x, .gv t, c', x' => t = s ∧ c = c' ∧ x = x' ∧ Chained c x s
  | .gu s, c, x, .go t, c', y =>
      (t = s ∧ c = c' ∧ x = y ∧ Chained c x s) ∨
        (c = c' ∧ Chained c x s ∧ Chained c' y t ∧ SuccOcc c y t x s)
  | .gv s, c, x, .go t, c', x' => t = s ∧ c = c' ∧ x = x' ∧ Chained c x s
  | .go s, c, x, .palF, _, _ => Chained c x s ∧ MaxOcc c x s
  | .go s, c, x, .palB, _, _ => Chained c x s
  | .spoil, c, c', .palT, _, _ => c = c' ∧ EmptyCl c
  | .spoil, c, c', .palF, _, _ => c = c' ∧ EmptyCl c
  | .spoil, c, c', .palB, _, _ => c = c' ∧ EmptyCl c
  | _, _, _, _, _, _ => False

/-! ### From a satisfying assignment to a proper coloring -/

open Classical in
/-- The coloring of the gadget graph induced by an assignment `ν`:
`0` is "true", `1` is "false", `2` is "base". -/
noncomputable def gadCol (ν : A → Prop) : SatTag → A → A → Fin 3
  | .palT, _, _ => 0
  | .palF, _, _ => 1
  | .palB, _, _ => 2
  | .lit s, a, _ => if LitTrue ν a s then 0 else 1
  | .gu s, c, x => if PrefixOrStrict ν c x s then 1 else if LitTrue ν x s then 2 else 0
  | .gv s, c, x => if PrefixOrStrict ν c x s then 2 else if LitTrue ν x s then 1 else 2
  | .go s, c, x => if PrefixOr ν c x s then 0 else 1
  | .spoil, _, _ => 2

/-- The coloring induced by a satisfying assignment is proper. -/
theorem gadCol_proper {ν : A → Prop}
    (hν : ∀ c : A, IsCl c → ∃ x s, OccIn c x s ∧ LitTrue ν x s)
    {t₁ t₂ : SatTag} {a₁ b₁ a₂ b₂ : A} (h : Core t₁ a₁ b₁ t₂ a₂ b₂) :
    gadCol ν t₁ a₁ b₁ ≠ gadCol ν t₂ a₂ b₂ := by
  cases t₁ <;> cases t₂ <;> simp only [Core] at h
  case palT.palF => simp only [gadCol]; decide
  case palF.palB => simp only [gadCol]; decide
  case palB.palT => simp only [gadCol]; decide
  case lit.lit s t =>
    obtain ⟨rfl, -, -, h3⟩ := h
    simp only [gadCol]
    rw [← h3, litTrue_not]
    split_ifs <;> simp_all
  case lit.palF s =>
    obtain ⟨-, c, hmin, hmax⟩ := h
    obtain ⟨z, u, hz, hT⟩ := hν c hmin.occIn.isCl
    obtain ⟨rfl, rfl⟩ := eq_of_minOcc_of_maxOcc hmin hmax hz
    simp only [gadCol, if_pos hT]
    decide
  case lit.palB s =>
    simp only [gadCol]
    split_ifs <;> decide
  case gu.lit s t =>
    obtain ⟨-, hch, hmin, hsucc⟩ := h
    have key := prefixOrStrict_of_min_succ (ν := ν) hmin hsucc
    simp only [gadCol]
    by_cases hA : PrefixOrStrict ν a₁ b₁ s
    · rw [if_pos hA, if_pos (key.mp hA)]; decide
    · rw [if_neg hA, if_neg (fun hT => hA (key.mpr hT))]
      split_ifs <;> decide
  case gu.gv s t =>
    obtain ⟨rfl, rfl, rfl, -⟩ := h
    simp only [gadCol]
    split_ifs <;> decide
  case gu.go s t =>
    rcases h with ⟨heq, rfl, rfl, hch⟩ | ⟨rfl, hchx, hchy, hsucc⟩
    · subst heq
      have hor := prefixOr_iff (ν := ν) hch.occIn
      simp only [gadCol]
      by_cases hA : PrefixOrStrict ν a₁ b₁ t
      · rw [if_pos hA, if_pos (hor.mpr (Or.inl hA))]; decide
      · rw [if_neg hA]
        by_cases hB : LitTrue ν b₁ t
        · rw [if_pos hB, if_pos (hor.mpr (Or.inr hB))]; decide
        · rw [if_neg hB, if_neg fun hO => (hor.mp hO).elim hA hB]; decide
    · have key := prefixOrStrict_succ (ν := ν) hsucc
      simp only [gadCol]
      by_cases hA : PrefixOrStrict ν a₁ b₁ s
      · rw [if_pos hA, if_pos (key.mp hA)]; decide
      · rw [if_neg hA, if_neg (fun hO => hA (key.mpr hO))]
        split_ifs <;> decide
  case gv.lit s t =>
    obtain ⟨rfl, -, rfl, -⟩ := h
    simp only [gadCol]
    split_ifs <;> decide
  case gv.go s t =>
    obtain ⟨heq, rfl, rfl, hch⟩ := h
    subst heq
    have hor := prefixOr_iff (ν := ν) hch.occIn
    simp only [gadCol]
    by_cases hA : PrefixOrStrict ν a₁ b₁ t
    · rw [if_pos hA, if_pos (hor.mpr (Or.inl hA))]; decide
    · rw [if_neg hA]
      by_cases hB : LitTrue ν b₁ t
      · rw [if_pos hB, if_pos (hor.mpr (Or.inr hB))]; decide
      · rw [if_neg hB, if_neg fun hO => (hor.mp hO).elim hA hB]; decide
  case go.palF s =>
    obtain ⟨hch, hmax⟩ := h
    obtain ⟨z, u, hz, hT⟩ := hν _ hch.occIn.isCl
    simp only [gadCol, if_pos (prefixOr_of_max hmax hz hT)]
    decide
  case go.palB s =>
    simp only [gadCol]
    split_ifs <;> decide
  case spoil.palT =>
    obtain ⟨-, hemp⟩ := h
    obtain ⟨z, u, hz, -⟩ := hν _ hemp.1
    exact absurd hz (hemp.2 z u)
  case spoil.palF =>
    obtain ⟨-, hemp⟩ := h
    obtain ⟨z, u, hz, -⟩ := hν _ hemp.1
    exact absurd hz (hemp.2 z u)
  case spoil.palB =>
    obtain ⟨-, hemp⟩ := h
    obtain ⟨z, u, hz, -⟩ := hν _ hemp.1
    exact absurd hz (hemp.2 z u)

/-! ### Main combinatorial equivalence -/

variable (A) in
/-- **Combinatorial correctness of the SAT → 3COL gadget**: a CNF structure is
satisfiable iff its gadget graph admits a proper 3-coloring. -/
theorem satisfiable_iff_gadColoring [Finite A] :
    Satisfiable A ↔
      ∃ col : SatTag → A → A → Fin 3,
        ∀ t₁ a₁ b₁ t₂ a₂ b₂, Core t₁ a₁ b₁ t₂ a₂ b₂ →
          col t₁ a₁ b₁ ≠ col t₂ a₂ b₂ := by
  constructor
  · rintro ⟨ν, hν⟩
    exact ⟨gadCol ν, fun t₁ a₁ b₁ t₂ a₂ b₂ h => gadCol_proper (satClauses_occ hν) h⟩
  · rintro ⟨col, hcol⟩
    rcases isEmpty_or_nonempty A with hA | ⟨⟨a₀⟩⟩
    · exact ⟨fun _ => True, fun c => (hA.false c).elim⟩
    -- palette colors and their rigidity
    set tc := col .palT a₀ a₀ with htc
    set fc := col .palF a₀ a₀ with hfc
    set bc := col .palB a₀ a₀ with hbc
    have hTF : tc ≠ fc := hcol .palT a₀ a₀ .palF a₀ a₀ trivial
    have hFB : fc ≠ bc := hcol .palF a₀ a₀ .palB a₀ a₀ trivial
    have hBT : bc ≠ tc := hcol .palB a₀ a₀ .palT a₀ a₀ trivial
    -- literal vertices are colored true-or-false, coherently with negation
    have hlitTF : ∀ (x : A) (s : Bool), col (.lit s) x x = tc ∨ col (.lit s) x x = fc := by
      intro x s
      have h1 : col (.lit s) x x ≠ bc := hcol (.lit s) x x .palB a₀ a₀ rfl
      rcases fin3_cases (col (.lit s) x x) tc fc bc hTF hFB hBT with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h h1
    have hlitne : ∀ (x : A) (s : Bool), col (.lit s) x x ≠ col (.lit (!s)) x x :=
      fun x s => hcol (.lit s) x x (.lit (!s)) x x ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨fun x => col (.lit true) x x = tc, ?_⟩
    intro c hc
    by_contra hno
    -- all literals of `c` are colored "false"
    have Hfalse : ∀ y t, OccIn c y t → col (.lit t) y y = fc := by
      intro y t hyt
      rcases hlitTF y t with hT | hF
      · refine absurd ?_ hno
        cases t with
        | false =>
          refine ⟨y, Or.inr ⟨hyt.2, fun hT' => hlitne y true (hT'.trans hT.symm)⟩⟩
        | true => exact ⟨y, Or.inl ⟨hyt.2, hT⟩⟩
      · exact hF
    by_cases hocc : ∃ y t, OccIn c y t
    · -- the chain of `c` is forced to "false", contradicting the forced output
      classical
      have step : ∀ x s, OccIn c x s →
          (∀ y t, OccIn c y t → occLt y t x s →
            (if MinOcc c y t then col (.lit t) y y else col (.go t) c y) = fc) →
          (if MinOcc c x s then col (.lit s) x x else col (.go s) c x) = fc := by
        intro x s hxs Hpred
        by_cases hmin : MinOcc c x s
        · rw [if_pos hmin]; exact Hfalse x s hxs
        · rw [if_neg hmin]
          obtain ⟨y, t, hsucc⟩ := exists_succOcc ⟨hxs, hmin⟩
          have ha := Hpred y t hsucc.1 hsucc.2.2.1
          have hu_ne : col (.gu s) c x ≠ fc := by
            by_cases hminy : MinOcc c y t
            · rw [if_pos hminy] at ha
              have h' := hcol (.gu s) c x (.lit t) y y ⟨rfl, ⟨hxs, hmin⟩, hminy, hsucc⟩
              rwa [ha] at h'
            · rw [if_neg hminy] at ha
              have h' := hcol (.gu s) c x (.go t) c y
                (Or.inr ⟨rfl, ⟨hxs, hmin⟩, ⟨hsucc.1, hminy⟩, hsucc⟩)
              rwa [ha] at h'
          have hv_ne : col (.gv s) c x ≠ fc := by
            have h' := hcol (.gv s) c x (.lit s) x x ⟨rfl, rfl, rfl, ⟨hxs, hmin⟩⟩
            rwa [Hfalse x s hxs] at h'
          have huv : col (.gu s) c x ≠ col (.gv s) c x :=
            hcol (.gu s) c x (.gv s) c x ⟨rfl, rfl, rfl, ⟨hxs, hmin⟩⟩
          have hou : col (.go s) c x ≠ col (.gu s) c x :=
            (hcol (.gu s) c x (.go s) c x (Or.inl ⟨rfl, rfl, rfl, ⟨hxs, hmin⟩⟩)).symm
          have hov : col (.go s) c x ≠ col (.gv s) c x :=
            (hcol (.gv s) c x (.go s) c x ⟨rfl, rfl, rfl, ⟨hxs, hmin⟩⟩).symm
          exact fin3_forced tc fc bc _ _ _ hTF hFB hBT hu_ne hv_ne huv hou hov
      have main : ∀ x : A, ∀ s, OccIn c x s →
          (if MinOcc c x s then col (.lit s) x x else col (.go s) c x) = fc := by
        intro x
        refine wellFounded_lt.induction
          (C := fun x => ∀ s, OccIn c x s →
            (if MinOcc c x s then col (.lit s) x x else col (.go s) c x) = fc) x ?_
        intro x IH s hxs
        refine step x s hxs fun y t hyt hlt => ?_
        rcases hlt with hlt | ⟨heq, hlt⟩
        · exact IH y hlt t hyt
        · rw [Bool.lt_iff] at hlt
          obtain ⟨rfl, rfl⟩ := hlt
          subst heq
          refine step y false hyt fun z u hz hlt' => ?_
          rcases hlt' with hlt' | ⟨heq', hlt'⟩
          · exact IH z hlt' u hz
          · simp [Bool.lt_iff] at hlt'
      obtain ⟨xm, sm, hmax⟩ := exists_maxOcc hocc
      have hm := main xm sm hmax.occIn
      by_cases hminm : MinOcc c xm sm
      · rw [if_pos hminm] at hm
        have h' := hcol (.lit sm) xm xm .palF a₀ a₀ ⟨rfl, c, hminm, hmax⟩
        rw [hm] at h'
        exact h' rfl
      · rw [if_neg hminm] at hm
        have h' := hcol (.go sm) c xm .palF a₀ a₀ ⟨⟨hmax.occIn, hminm⟩, hmax⟩
        rw [hm] at h'
        exact h' rfl
    · -- empty clause: the spoiler needs a fourth color
      have hemp : EmptyCl c := ⟨hc, fun y t hyt => hocc ⟨y, t, hyt⟩⟩
      have h1 := hcol .spoil c c .palT a₀ a₀ ⟨rfl, hemp⟩
      have h2 := hcol .spoil c c .palF a₀ a₀ ⟨rfl, hemp⟩
      have h3 := hcol .spoil c c .palB a₀ a₀ ⟨rfl, hemp⟩
      rcases fin3_cases (col .spoil c c) tc fc bc hTF hFB hBT with h | h | h
      exacts [h1 h, h2 h, h3 h]

end SatToCol

end FirstOrder
