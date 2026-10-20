/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.CycleCover.Models
import DescriptiveComplexity.Permanent.Widths
import DescriptiveComplexity.OccurrenceFormulas
import DescriptiveComplexity.OrderedComposition
import DescriptiveComplexity.RelComposition
import DescriptiveComplexity.Syntax

/-!
# The formulas of the reduction of #1-in-SAT to #Cycle Cover

The reduction draws, over the ordered expansion of a CNF formula, the ladder
expansion (`DescriptiveComplexity.ladder`) of the base graph with Valiant's
gadgets attached (`DescriptiveComplexity.Site.flatAttach`). This file names
the tags and writes the first-order formulas the drawing is made of, each
with its realization lemma; the drawing itself is in
`DescriptiveComplexity.Problems.CycleCover.Drawing`.

* A **node** of the attached graph is a tagged pair `(c, x)`: a track node, a
  spoke or a gadget node of the occurrence of the literal `(x, s)` in the
  clause `c` (the dummy occurrence of `x` being written `(x, x)`), or the hub
  of the clause `c` or of the variable `x` (written `(c, c)` and `(x, x)`).
  `DescriptiveComplexity.SatCover.vDomF` says which pairs are nodes of which
  tag, `DescriptiveComplexity.SatCover.flatEntryF` which entries the attached
  matrix has between them.
* A **level** of the ladders is a tagged pair too: one level per occurrence
  and index in `Fin 3`, and one more, the pair of least elements. The levels
  are ordered lexicographically (`DescriptiveComplexity.SatCover.levelLeF`),
  and the least level, the greatest and the cover relation are first-order.
* A **rung** is a node, a node, a level and an index below the width
  (`DescriptiveComplexity.SatCover.widthF`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure SatOcc Finset

namespace SatCover

/-! ### Tags -/

/-- The tag of an occurrence: whether it is the dummy one, and its sign. -/
abbrev OccTag : Type := Bool × Bool

/-- The tags of the nodes of the base graph: track nodes and spokes of an
occurrence, and hubs, of a clause (`true`) or of a variable (`false`). -/
abbrev NodeTag : Type := OccTag ⊕ OccTag ⊕ Bool

/-- The tags of the nodes of the attached graph: base nodes, and the four
gadget nodes of an occurrence. -/
abbrev VTag : Type := NodeTag ⊕ (OccTag × Fin 4)

/-- The tags of the levels: one per occurrence and index, and one more. A
definition rather than an abbreviation, so that the only order on it is the
one declared here. -/
def LevelTag : Type := Option (OccTag × Fin 3)

instance : Finite LevelTag := inferInstanceAs (Finite (Option (OccTag × Fin 3)))

instance : DecidableEq LevelTag := inferInstanceAs (DecidableEq (Option (OccTag × Fin 3)))

noncomputable instance : LinearOrder LevelTag := finiteLinearOrder LevelTag

/-- The extra level. -/
def LevelTag.extra : LevelTag := (none : Option (OccTag × Fin 3))

/-- The level of an occurrence tag and an index. -/
def LevelTag.pos (o : OccTag) (k : Fin 3) : LevelTag := (some (o, k) : Option (OccTag × Fin 3))

/-- The tags of the drawing: the nodes of the attached graph, and the rungs,
tagged by their two nodes, their level and their index. -/
abbrev DrawTag : Type := VTag ⊕ (VTag × VTag × LevelTag × Fin 3)

/-! ### Occurrences and nodes -/

section Builders

variable {α : Type}

/-- `x` is a variable of the formula, as a formula. -/
noncomputable def satOccF (x : α) : satOrd.Formula α :=
  fo%[x] ∃ c, clF⟨c⟩ ∧ (posF⟨c, x⟩ ∨ negF⟨c, x⟩)

/-- `(c, x)` is an occurrence of tag `(d, s)`: the dummy occurrence `(x, x)`
of a variable `x` when `d`, the occurrence of `(x, s)` in the clause `c`
otherwise. -/
noncomputable def occDomF (d s : Bool) (c x : α) : satOrd.Formula α :=
  if d then eqF c x ⊓ satOccF x else occF s c x

/-- `(c, x)` is a node of the base graph of tag `t`. -/
noncomputable def nodeDomF (t : NodeTag) (c x : α) : satOrd.Formula α :=
  match t with
  | Sum.inl (d, s) => occDomF d s c x
  | Sum.inr (Sum.inl (d, s)) => occDomF d s c x
  | Sum.inr (Sum.inr true) => clF c ⊓ eqF x c
  | Sum.inr (Sum.inr false) => satOccF c ⊓ eqF x c

/-- `(c, x)` is a node of the attached graph of tag `t`. -/
noncomputable def vDomF (t : VTag) (c x : α) : satOrd.Formula α :=
  match t with
  | Sum.inl t => nodeDomF t c x
  | Sum.inr ((d, s), _) => occDomF d s c x

/-- `c` is the least element, as a formula. -/
noncomputable def isMinF (c : α) : satOrd.Formula α :=
  fo%[c] ∀ y, leF⟨c, y⟩

/-- `(c, x)` is a level of tag `t`: an occurrence, or the pair of least
elements. -/
noncomputable def levelDomF (t : LevelTag) (c x : α) : satOrd.Formula α :=
  match (t : Option (OccTag × Fin 3)) with
  | none => isMinF c ⊓ eqF x c
  | some ((d, s), _) => occDomF d s c x

/-! ### The base edges and the entries of the attached matrix -/

/-- `(c', x)` is the occurrence of the literal `(x, s)` next after `(c, x)`,
cyclically, the dummy occurrence first: the four cases according to whether
each is the dummy one. -/
noncomputable def nextF (d d' s : Bool) (c x c' : α) : satOrd.Formula α :=
  match d, d' with
  | true, true => fo%[c, x, c'] ∀ y, ¬ (occF s)⟨y, x⟩
  | true, false => fo%[c, x, c'] ∀ y, (occF s)⟨y, x⟩ → leF⟨c', y⟩
  | false, true => fo%[c, x, c'] ∀ y, (occF s)⟨y, x⟩ → leF⟨y, c⟩
  | false, false => fo%[c, x, c'] ltF⟨c, c'⟩ ∧ ∀ y, (occF s)⟨y, x⟩ → ltF⟨c, y⟩ → leF⟨c', y⟩

/-- The base edge from the node `(c, x)` of tag `t` to the node `(c', x')` of
tag `t'`. -/
noncomputable def baseEdgeF (t t' : NodeTag) (c x c' x' : α) : satOrd.Formula α :=
  match t, t' with
  | Sum.inl (d, s), Sum.inl (d', s') =>
      if s = s' then eqF x x' ⊓ nextF d d' s c x c' else ⊥
  | Sum.inr (Sum.inl (d, _)), Sum.inr (Sum.inr b) =>
      if d then (if b then ⊥ else eqF x c') else if b then eqF c c' else ⊥
  | Sum.inr (Sum.inr b), Sum.inr (Sum.inl (d, _)) =>
      if d then (if b then ⊥ else eqF c x') else if b then eqF c c' else ⊥
  | _, _ => ⊥

/-- The entry of the attached matrix between the node `(c, x)` of tag `t` and
the node `(c', x')` of tag `t'` is `v`, for `v ≠ 0`. -/
noncomputable def flatEntryF (v : ℤ) (t t' : VTag) (c x c' x' : α) : satOrd.Formula α :=
  match t, t' with
  | Sum.inl t, Sum.inl t' => if v = 1 then baseEdgeF t t' c x c' x' else ⊥
  | Sum.inl t, Sum.inr (o, j) =>
      if v = 1 ∧ ((t = Sum.inl o ∧ j = 0) ∨ (t = Sum.inr (Sum.inl o) ∧ j = 3)) then
        eqF c c' ⊓ eqF x x'
      else ⊥
  | Sum.inr (o, j), Sum.inl t' =>
      if v = 1 ∧ ((j = 3 ∧ t' = Sum.inl o) ∨ (j = 0 ∧ t' = Sum.inr (Sum.inl o))) then
        eqF c c' ⊓ eqF x x'
      else ⊥
  | Sum.inr (o, j), Sum.inr (o', j') =>
      if o = o' ∧ xorGadget j j' = v then eqF c c' ⊓ eqF x x' else ⊥

/-! ### The order of the levels -/

/-- The level `(c, x)` of tag `t` is at most the level `(c', x')` of tag `t'`,
in the lexicographic order: the tags are compared statically. -/
noncomputable def levelLeF (t t' : LevelTag) (c x c' x' : α) : satOrd.Formula α :=
  if t < t' then ⊤ else if t' < t then ⊥ else ltF c c' ⊔ (eqF c c' ⊓ leF x x')

/-- Strictly below, among the levels. -/
noncomputable def levelLtF (t t' : LevelTag) (c x c' x' : α) : satOrd.Formula α :=
  levelLeF t t' c x c' x' ⊓ ∼(levelLeF t' t c' x' c x)

/-- The level `(c, x)` of tag `t` is the least level. -/
noncomputable def levelMinF (t : LevelTag) (c x : α) : satOrd.Formula α :=
  fo%[c, x] ⋀ t' : LevelTag, ∀ c' x', (levelDomF t')⟨c', x'⟩ → (levelLeF t t')⟨c, x, c', x'⟩

/-- The level `(c, x)` of tag `t` is the greatest level. -/
noncomputable def levelMaxF (t : LevelTag) (c x : α) : satOrd.Formula α :=
  fo%[c, x] ⋀ t' : LevelTag, ∀ c' x', (levelDomF t')⟨c', x'⟩ → (levelLeF t' t)⟨c', x', c, x⟩

/-- The level `(c', x')` of tag `t'` is the one next after the level `(c, x)`
of tag `t`. -/
noncomputable def levelCovF (t t' : LevelTag) (c x c' x' : α) : satOrd.Formula α :=
  fo%[c, x, c', x'] (levelLtF t t')⟨c, x, c', x'⟩ ∧
    ¬ ⋁ t'' : LevelTag, ∃ c'' x'', (levelDomF t'')⟨c'', x''⟩ ∧
      (levelLtF t t'')⟨c, x, c'', x''⟩ ∧ (levelLtF t'' t')⟨c'', x'', c', x'⟩

/-! ### The widths -/

/-- The index `j` is below the width, at the level `(c'', x'')` of tag `l`,
of the ladder from the node `(c, x)` of tag `t` to the node `(c', x')` of
tag `t'`: two rungs at every level for an entry `-1`, the entry at the
least level and one rung elsewhere otherwise. -/
noncomputable def widthF (t t' : VTag) (l : LevelTag) (j : Fin 3) (c x c' x' c'' x'' : α) :
    satOrd.Formula α :=
  (flatEntryF (-1) t t' c x c' x' ⊓ (if j.val < 2 then ⊤ else ⊥)) ⊔
    (∼(flatEntryF (-1) t t' c x c' x') ⊓
      ((levelMinF l c'' x'' ⊓
          ((if j.val < 1 then flatEntryF 1 t t' c x c' x' else ⊥) ⊔
            ((if j.val < 2 then flatEntryF 2 t t' c x c' x' else ⊥) ⊔
              (if j.val < 3 then flatEntryF 3 t t' c x c' x' else ⊥)))) ⊔
        (∼(levelMinF l c'' x'') ⊓ (if j.val < 1 then ⊤ else ⊥))))

end Builders

/-! ### Semantics of the tags -/

section Semantics

variable {A : Type} [Language.sat.Structure A]

/-- The pair `(c, x)` is an occurrence of tag `(d, s)`. -/
def OccDom (d s : Bool) (c x : A) : Prop :=
  if d then c = x ∧ SatOccurs A x else OccIn c x s

/-- The clause of an occurrence of tag `d`: `⊥` for the dummy one. -/
def occC (d : Bool) (c : A) : WithBot A :=
  if d then ⊥ else c

/-- The occurrence a tagged pair denotes. -/
def occOf (d s : Bool) (c x : A) (h : OccDom d s c x) : Occ A :=
  ⟨(occC d c, x, s), by
    cases d
    · exact Or.inr ⟨c, rfl, h⟩
    · exact Or.inl ⟨rfl, h.2⟩⟩

@[simp] theorem occOf_c (d s : Bool) (c x : A) (h : OccDom d s c x) :
    (occOf d s c x h).c = occC d c := rfl

@[simp] theorem occOf_x (d s : Bool) (c x : A) (h : OccDom d s c x) :
    (occOf d s c x h).x = x := rfl

@[simp] theorem occOf_s (d s : Bool) (c x : A) (h : OccDom d s c x) :
    (occOf d s c x h).s = s := rfl

/-- The tag of an occurrence. -/
def occTag (o : Occ A) : OccTag :=
  (WithBot.recBotCoe true (fun _ => false) o.c, o.s)

/-- The pair an occurrence is drawn as: `(x, x)` for a dummy one. -/
def occPair (o : Occ A) : A × A :=
  (o.c.unbotD o.x, o.x)

theorem occTag_of_bot {o : Occ A} (hb : o.c = ⊥) : occTag o = (true, o.s) := by
  rw [occTag, hb, WithBot.recBotCoe_bot]

theorem occTag_of_coe {o : Occ A} {c : A} (hc : o.c = c) : occTag o = (false, o.s) := by
  rw [occTag, hc, WithBot.recBotCoe_coe]

theorem occPair_of_bot {o : Occ A} (hb : o.c = ⊥) : occPair o = (o.x, o.x) := by
  rw [occPair, hb, WithBot.unbotD_bot]

theorem occPair_of_coe {o : Occ A} {c : A} (hc : o.c = c) : occPair o = (c, o.x) := by
  rw [occPair, hc, WithBot.unbotD_coe]

theorem occDom_occTag (o : Occ A) :
    OccDom (occTag o).1 (occTag o).2 (occPair o).1 (occPair o).2 := by
  rcases o.2 with ⟨hb, hx⟩ | ⟨c, hc, h⟩
  · rw [occTag_of_bot hb, occPair_of_bot hb]
    exact ⟨rfl, hx⟩
  · rw [occTag_of_coe hc, occPair_of_coe hc]
    exact h

theorem occOf_occTag (o : Occ A) :
    occOf (occTag o).1 (occTag o).2 (occPair o).1 (occPair o).2 (occDom_occTag o) = o := by
  refine Occ.ext ?_ rfl rfl
  rw [occOf_c]
  rcases o.2 with ⟨hb, _⟩ | ⟨c, hc, _⟩
  · rw [occTag_of_bot hb, occPair_of_bot hb]
    exact hb.symm
  · rw [occTag_of_coe hc, occPair_of_coe hc]
    exact hc.symm

theorem occTag_occOf (d s : Bool) (c x : A) (h : OccDom d s c x) :
    occTag (occOf d s c x h) = (d, s) := by
  cases d
  · exact occTag_of_coe (c := c) rfl
  · exact occTag_of_bot rfl

theorem occPair_occOf (d s : Bool) (c x : A) (h : OccDom d s c x) :
    occPair (occOf d s c x h) = (c, x) := by
  cases d
  · exact occPair_of_coe (c := c) rfl
  · rw [occPair_of_bot rfl]
    exact Prod.ext h.1.symm rfl

/-- The pair `(c, x)` is a node of the base graph of tag `t`. -/
def NodeDom (t : NodeTag) (c x : A) : Prop :=
  match t with
  | Sum.inl (d, s) => OccDom d s c x
  | Sum.inr (Sum.inl (d, s)) => OccDom d s c x
  | Sum.inr (Sum.inr true) => IsCl c ∧ x = c
  | Sum.inr (Sum.inr false) => SatOccurs A c ∧ x = c

/-- The node a tagged pair denotes. -/
def nodeOf (t : NodeTag) (c x : A) (h : NodeDom t c x) : Node A :=
  match t, h with
  | Sum.inl (d, s), h => trk (occOf d s c x h)
  | Sum.inr (Sum.inl (d, s)), h => spk (occOf d s c x h)
  | Sum.inr (Sum.inr true), h => hub (Sum.inl ⟨c, h.1⟩)
  | Sum.inr (Sum.inr false), h => hub (Sum.inr ⟨c, h.1⟩)

/-- The tag of a node. -/
def nodeTag (n : Node A) : NodeTag :=
  match n with
  | Sum.inl o => Sum.inl (occTag o)
  | Sum.inr (Sum.inl o) => Sum.inr (Sum.inl (occTag o))
  | Sum.inr (Sum.inr (Sum.inl _)) => Sum.inr (Sum.inr true)
  | Sum.inr (Sum.inr (Sum.inr _)) => Sum.inr (Sum.inr false)

/-- The pair a node is drawn as. -/
def nodePair (n : Node A) : A × A :=
  match n with
  | Sum.inl o => occPair o
  | Sum.inr (Sum.inl o) => occPair o
  | Sum.inr (Sum.inr (Sum.inl c)) => (c.1, c.1)
  | Sum.inr (Sum.inr (Sum.inr x)) => (x.1, x.1)

theorem nodeDom_nodeTag (n : Node A) : NodeDom (nodeTag n) (nodePair n).1 (nodePair n).2 := by
  rcases n with o | o | c | x
  · exact occDom_occTag o
  · exact occDom_occTag o
  · exact ⟨c.2, rfl⟩
  · exact ⟨x.2, rfl⟩

theorem nodeOf_nodeTag (n : Node A) :
    nodeOf (nodeTag n) (nodePair n).1 (nodePair n).2 (nodeDom_nodeTag n) = n := by
  rcases n with o | o | c | x
  · exact congrArg trk (occOf_occTag o)
  · exact congrArg spk (occOf_occTag o)
  · rfl
  · rfl

theorem nodeTag_nodeOf (t : NodeTag) (c x : A) (h : NodeDom t c x) :
    nodeTag (nodeOf t c x h) = t := by
  rcases t with ⟨d, s⟩ | ⟨d, s⟩ | _ | _
  · exact congrArg Sum.inl (occTag_occOf d s c x h)
  · exact congrArg (fun o => Sum.inr (Sum.inl o)) (occTag_occOf d s c x h)
  · rfl
  · rfl

theorem nodePair_nodeOf (t : NodeTag) (c x : A) (h : NodeDom t c x) :
    nodePair (nodeOf t c x h) = (c, x) := by
  rcases t with ⟨d, s⟩ | ⟨d, s⟩ | _ | _
  · exact occPair_occOf d s c x h
  · exact occPair_occOf d s c x h
  · exact Prod.ext rfl h.2.symm
  · exact Prod.ext rfl h.2.symm

/-- The nodes of the attached graph. -/
abbrev V (A : Type) [Language.sat.Structure A] : Type :=
  Node A ⊕ (Occ A × Fin 4)

/-- The pair `(c, x)` is a node of the attached graph of tag `t`. -/
def VDom (t : VTag) (c x : A) : Prop :=
  match t with
  | Sum.inl t => NodeDom t c x
  | Sum.inr ((d, s), _) => OccDom d s c x

/-- The node of the attached graph a tagged pair denotes. -/
def vOf (t : VTag) (c x : A) (h : VDom t c x) : V A :=
  match t, h with
  | Sum.inl t, h => Sum.inl (nodeOf t c x h)
  | Sum.inr ((d, s), j), h => Sum.inr (occOf d s c x h, j)

/-- The tag of a node of the attached graph. -/
def vTag (n : V A) : VTag :=
  match n with
  | Sum.inl n => Sum.inl (nodeTag n)
  | Sum.inr (o, j) => Sum.inr (occTag o, j)

/-- The pair a node of the attached graph is drawn as. -/
def vPair (n : V A) : A × A :=
  match n with
  | Sum.inl n => nodePair n
  | Sum.inr (o, _) => occPair o

theorem vDom_vTag (n : V A) : VDom (vTag n) (vPair n).1 (vPair n).2 := by
  rcases n with n | ⟨o, j⟩
  · exact nodeDom_nodeTag n
  · exact occDom_occTag o

theorem vOf_vTag (n : V A) : vOf (vTag n) (vPair n).1 (vPair n).2 (vDom_vTag n) = n := by
  rcases n with n | ⟨o, j⟩
  · exact congrArg Sum.inl (nodeOf_nodeTag n)
  · exact congrArg (fun o => Sum.inr (o, j)) (occOf_occTag o)

theorem vTag_vOf (t : VTag) (c x : A) (h : VDom t c x) : vTag (vOf t c x h) = t := by
  rcases t with t | ⟨⟨d, s⟩, j⟩
  · exact congrArg Sum.inl (nodeTag_nodeOf t c x h)
  · exact congrArg (fun o => Sum.inr (o, j)) (occTag_occOf d s c x h)

theorem vPair_vOf (t : VTag) (c x : A) (h : VDom t c x) : vPair (vOf t c x h) = (c, x) := by
  rcases t with t | ⟨⟨d, s⟩, j⟩
  · exact nodePair_nodeOf t c x h
  · exact occPair_occOf d s c x h

/-- The pair `(c, x)` is a level of tag `t`. -/
def LevelDom [LE A] (t : LevelTag) (c x : A) : Prop :=
  match (t : Option (OccTag × Fin 3)) with
  | none => (∀ y, c ≤ y) ∧ x = c
  | some ((d, s), _) => OccDom d s c x

end Semantics

/-! ### Realization -/

section Realize

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {α : Type} {v : α → A}

theorem realize_satOccF {x : α} : (satOccF x).Realize v ↔ SatOccurs A (v x) := by
  simp only [satOccF, Formula.realize_iExs, Formula.realize_inf, Formula.realize_sup, realize_clF,
    realize_posF, realize_negF, Sum.elim_inl, Sum.elim_inr, SatOccurs, IsCl, PosIn, NegIn]
  exact ⟨fun ⟨c, h⟩ => ⟨c 0, h⟩, fun ⟨c, h⟩ => ⟨fun _ => c, h⟩⟩

theorem realize_occDomF {d s : Bool} {c x : α} :
    (occDomF d s c x).Realize v ↔ OccDom d s (v c) (v x) := by
  cases d <;> simp [occDomF, OccDom, realize_eqF, realize_satOccF]

theorem realize_nodeDomF {t : NodeTag} {c x : α} :
    (nodeDomF t c x).Realize v ↔ NodeDom t (v c) (v x) := by
  rcases t with ⟨d, s⟩ | ⟨d, s⟩ | b
  · exact realize_occDomF
  · exact realize_occDomF
  · cases b <;> simp [nodeDomF, NodeDom, realize_eqF, realize_satOccF, realize_clF]

theorem realize_vDomF {t : VTag} {c x : α} : (vDomF t c x).Realize v ↔ VDom t (v c) (v x) := by
  rcases t with t | ⟨⟨d, s⟩, j⟩
  · exact realize_nodeDomF
  · exact realize_occDomF

theorem realize_isMinF {c : α} : (isMinF c).Realize v ↔ ∀ y, v c ≤ y := by
  simp only [isMinF, Formula.realize_iAlls, realize_leF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h y => h fun _ => y, fun h y => h (y 0)⟩

theorem realize_levelDomF {t : LevelTag} {c x : α} :
    (levelDomF t c x).Realize v ↔ LevelDom t (v c) (v x) := by
  rcases (t : Option (OccTag × Fin 3)) with _ | ⟨⟨d, s⟩, k⟩
  · simp [levelDomF, LevelDom, realize_isMinF, realize_eqF]
  · exact realize_occDomF

/-! #### The next occurrence -/

variable [Fintype A]

theorem mem_above_chain {x : A} {s : Bool} {a y : WithBot A} :
    y ∈ above (chain x s) a ↔ (y = ⊥ ∨ ∃ y₀ : A, y = y₀ ∧ OccIn y₀ x s) ∧ a < y := by
  rw [mem_above, mem_chain]

theorem realize_nextF {d d' s : Bool} {c x c' : α} (h : OccDom d s (v c) (v x))
    (h' : OccDom d' s (v c') (v x)) :
    (nextF d d' s c x c').Realize v ↔
      cycNext (chain (v x) s) (occC d (v c)) = occC d' (v c') := by
  cases d <;> cases d' <;>
    simp only [nextF, Formula.realize_iAlls, Formula.realize_imp, Formula.realize_not,
      Formula.realize_inf, realize_occF, realize_leF, realize_ltF, Sum.elim_inl, Sum.elim_inr,
      occC, ↓reduceIte, Bool.false_eq_true]
  · -- real to real
    change OccIn (v c) (v x) s at h
    change OccIn (v c') (v x) s at h'
    constructor
    · rintro ⟨hlt, hall⟩
      have hne : (above (chain (v x) s) (v c)).Nonempty :=
        ⟨v c', mem_above_chain.mpr ⟨Or.inr ⟨_, rfl, h'⟩, WithBot.coe_lt_coe.mpr hlt⟩⟩
      rw [cycNext_of_nonempty hne]
      refine le_antisymm (min'_le _ _ (mem_above_chain.mpr ⟨Or.inr ⟨_, rfl, h'⟩,
        WithBot.coe_lt_coe.mpr hlt⟩)) (le_min' _ _ _ fun y hy => ?_)
      obtain ⟨hb | ⟨y₀, rfl, hy₀⟩, hlt'⟩ := mem_above_chain.mp hy
      · exact absurd (hb ▸ hlt') not_lt_bot
      · exact WithBot.coe_le_coe.mpr (hall (fun _ => y₀) hy₀ (WithBot.coe_lt_coe.mp hlt'))
    · intro heq
      by_cases hne : (above (chain (v x) s) (v c)).Nonempty
      · rw [cycNext_of_nonempty hne] at heq
        have hmem := heq ▸ min'_mem _ hne
        obtain ⟨-, hlt⟩ := mem_above_chain.mp hmem
        refine ⟨WithBot.coe_lt_coe.mp hlt, fun y hy hlt' => WithBot.coe_le_coe.mp ?_⟩
        rw [← heq]
        exact min'_le _ _ (mem_above_chain.mpr ⟨Or.inr ⟨_, rfl, hy⟩, WithBot.coe_lt_coe.mpr hlt'⟩)
      · rw [cycNext_of_not_nonempty hne (chain_nonempty _ _)] at heq
        exact absurd (heq ▸ min'_le _ _ (mem_chain.mpr (Or.inl rfl)) : (v c' : WithBot A) ≤ ⊥)
          (WithBot.coe_ne_bot ∘ le_bot_iff.mp)
  · -- real to dummy
    change OccIn (v c) (v x) s at h
    constructor
    · intro hall
      have hne : ¬(above (chain (v x) s) (v c)).Nonempty := by
        rintro ⟨y, hy⟩
        obtain ⟨hb | ⟨y₀, rfl, hy₀⟩, hlt⟩ := mem_above_chain.mp hy
        · exact absurd (hb ▸ hlt) not_lt_bot
        · exact (hall (fun _ => y₀) hy₀).not_gt (WithBot.coe_lt_coe.mp hlt)
      rw [cycNext_of_not_nonempty hne (chain_nonempty _ _)]
      exact le_antisymm (min'_le _ _ (mem_chain.mpr (Or.inl rfl))) bot_le
    · intro heq y hy
      by_contra hlt
      rw [not_le] at hlt
      have hne : (above (chain (v x) s) (v c)).Nonempty :=
        ⟨y 0, mem_above_chain.mpr ⟨Or.inr ⟨_, rfl, hy⟩, WithBot.coe_lt_coe.mpr hlt⟩⟩
      rw [cycNext_of_nonempty hne] at heq
      obtain ⟨-, hlt'⟩ := mem_above_chain.mp (heq ▸ min'_mem _ hne)
      exact not_lt_bot hlt'
  · -- dummy to real
    change OccIn (v c') (v x) s at h'
    have hne : (above (chain (v x) s) ⊥).Nonempty :=
      ⟨v c', mem_above_chain.mpr ⟨Or.inr ⟨_, rfl, h'⟩, WithBot.bot_lt_coe _⟩⟩
    rw [cycNext_of_nonempty hne]
    constructor
    · intro hall
      refine le_antisymm (min'_le _ _ (mem_above_chain.mpr ⟨Or.inr ⟨_, rfl, h'⟩,
        WithBot.bot_lt_coe _⟩)) (le_min' _ _ _ fun y hy => ?_)
      obtain ⟨hb | ⟨y₀, rfl, hy₀⟩, hlt⟩ := mem_above_chain.mp hy
      · exact absurd (hb ▸ hlt) not_lt_bot
      · exact WithBot.coe_le_coe.mpr (hall (fun _ => y₀) hy₀)
    · intro heq y hy
      refine WithBot.coe_le_coe.mp ?_
      rw [← heq]
      exact min'_le _ _ (mem_above_chain.mpr ⟨Or.inr ⟨_, rfl, hy⟩, WithBot.bot_lt_coe _⟩)
  · -- dummy to dummy
    constructor
    · intro hall
      have hne : ¬(above (chain (v x) s) ⊥).Nonempty := by
        rintro ⟨y, hy⟩
        obtain ⟨hb | ⟨y₀, rfl, hy₀⟩, hlt⟩ := mem_above_chain.mp hy
        · exact absurd (hb ▸ hlt) not_lt_bot
        · exact hall (fun _ => y₀) hy₀
      rw [cycNext_of_not_nonempty hne (chain_nonempty _ _)]
      exact le_antisymm (min'_le _ _ (mem_chain.mpr (Or.inl rfl))) bot_le
    · intro heq y hy
      have hne : (above (chain (v x) s) ⊥).Nonempty :=
        ⟨y 0, mem_above_chain.mpr ⟨Or.inr ⟨_, rfl, hy⟩, WithBot.bot_lt_coe _⟩⟩
      rw [cycNext_of_nonempty hne] at heq
      obtain ⟨-, hlt'⟩ := mem_above_chain.mp (heq ▸ min'_mem _ hne)
      exact not_lt_bot hlt'

/-! #### The base edges -/

/-- The kind of a node: track node, spoke or hub. -/
def nodeKind (n : Node A) : Fin 3 :=
  match n with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

/-- The kind of a node tag. -/
def tagKind (t : NodeTag) : Fin 3 :=
  match t with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

omit [LinearOrder A] [Fintype A] in
theorem nodeKind_nodeOf (t : NodeTag) (c x : A) (h : NodeDom t c x) :
    nodeKind (nodeOf t c x h) = tagKind t := by
  rcases t with _ | _ | b
  · rfl
  · rfl
  · cases b <;> rfl

/-- The kinds of the ends of a base edge: along a track, from a spoke to a
hub, or from a hub to a spoke. -/
theorem baseEdge_kind {n n' : Node A} (h : BaseEdge n n') :
    (nodeKind n = 0 ∧ nodeKind n' = 0) ∨ (nodeKind n = 1 ∧ nodeKind n' = 2) ∨
      (nodeKind n = 2 ∧ nodeKind n' = 1) := by
  cases h with
  | track o => exact Or.inl ⟨rfl, rfl⟩
  | spoke o => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | hub o => exact Or.inr (Or.inr ⟨rfl, rfl⟩)

omit [LinearOrder A] [Fintype A] in
/-- An occurrence is determined by its tag and its pair. -/
theorem occOf_eq_iff {d s d' s' : Bool} {c x c' x' : A} (h : OccDom d s c x)
    (h' : OccDom d' s' c' x') :
    occOf d s c x h = occOf d' s' c' x' h' ↔ (d, s) = (d', s') ∧ (c, x) = (c', x') := by
  constructor
  · intro he
    refine ⟨?_, ?_⟩
    · rw [← occTag_occOf d s c x h, he, occTag_occOf]
    · rw [← occPair_occOf d s c x h, he, occPair_occOf]
  · rintro ⟨h1, h2⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    rfl

omit [LinearOrder A] [Fintype A] in
/-- A node is determined by its tag and its pair. -/
theorem nodeOf_eq_iff {t t' : NodeTag} {c x c' x' : A} (h : NodeDom t c x)
    (h' : NodeDom t' c' x') :
    nodeOf t c x h = nodeOf t' c' x' h' ↔ t = t' ∧ (c, x) = (c', x') := by
  constructor
  · intro he
    refine ⟨?_, ?_⟩
    · rw [← nodeTag_nodeOf t c x h, he, nodeTag_nodeOf]
    · rw [← nodePair_nodeOf t c x h, he, nodePair_nodeOf]
  · rintro ⟨rfl, h2⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
    rfl

/-- No base edge between nodes whose kinds do not match. -/
theorem not_baseEdge_of_kind {t t' : NodeTag} {c x c' x' : A} (h : NodeDom t c x)
    (h' : NodeDom t' c' x')
    (hk : ¬((tagKind t = 0 ∧ tagKind t' = 0) ∨ (tagKind t = 1 ∧ tagKind t' = 2) ∨
      (tagKind t = 2 ∧ tagKind t' = 1))) :
    ¬BaseEdge (nodeOf t c x h) (nodeOf t' c' x' h') := fun he =>
  hk (by simpa only [nodeKind_nodeOf] using baseEdge_kind he)

/-- The base edge from a spoke to a hub, read on the tags. -/
theorem baseEdge_spk_hub_iff {d s : Bool} {c x : A} (h : OccDom d s c x) (k : Hub A) :
    BaseEdge (spk (occOf d s c x h)) (hub k) ↔ hubOf (occOf d s c x h) = k := by
  rw [baseEdge_spk_iff]
  exact ⟨fun h => (Sum.inr.inj (Sum.inr.inj h)).symm, fun h => congrArg hub h.symm⟩

/-- The base edge from a hub to a spoke, read on the tags. -/
theorem baseEdge_hub_spk_iff (k : Hub A) {d s : Bool} {c x : A} (h : OccDom d s c x) :
    BaseEdge (hub k) (spk (occOf d s c x h)) ↔ hubOf (occOf d s c x h) = k := by
  rw [baseEdge_hub_iff]
  exact ⟨fun ⟨o, ho, hk⟩ => (Sum.inl.inj (Sum.inr.inj ho)) ▸ hk, fun hk => ⟨_, rfl, hk⟩⟩

theorem realize_baseEdgeF {t t' : NodeTag} {c x c' x' : α} (h : NodeDom t (v c) (v x))
    (h' : NodeDom t' (v c') (v x')) :
    (baseEdgeF t t' c x c' x').Realize v ↔
      BaseEdge (nodeOf t (v c) (v x) h) (nodeOf t' (v c') (v x') h') := by
  rcases t with ⟨d, s⟩ | ⟨d, s⟩ | b <;> rcases t' with ⟨d', s'⟩ | ⟨d', s'⟩ | b'
  · -- track to track
    change OccDom d s (v c) (v x) at h
    change OccDom d' s' (v c') (v x') at h'
    simp only [baseEdgeF, nodeOf, baseEdge_trk_iff, trk, Sum.inl.injEq]
    split_ifs with hs
    · subst hs
      rw [Formula.realize_inf, realize_eqF]
      constructor
      · rintro ⟨hx, hn⟩
        have h'' : OccDom d' s (v c') (v x) := hx ▸ h'
        rw [realize_nextF h h''] at hn
        exact Occ.ext (by rw [occOf_c, nextOcc_c, occOf_c, occOf_x, occOf_s, hn]) hx.symm rfl
      · intro he
        have hx : v x = v x' := (congrArg Occ.x he).symm
        have h'' : OccDom d' s (v c') (v x) := hx ▸ h'
        refine ⟨hx, (realize_nextF h h'').mpr ?_⟩
        have := congrArg Occ.c he
        rw [occOf_c, nextOcc_c, occOf_c, occOf_x, occOf_s] at this
        exact this.symm
    · simp only [Formula.realize_bot, false_iff]
      intro he
      have := congrArg Occ.s he
      rw [occOf_s, nextOcc_s, occOf_s] at this
      exact hs this.symm
  · exact iff_of_false (by simp [baseEdgeF]) (not_baseEdge_of_kind h h' (by simp [tagKind]))
  · exact iff_of_false (by simp [baseEdgeF]) (not_baseEdge_of_kind h h' (by simp [tagKind]))
  · exact iff_of_false (by simp [baseEdgeF]) (not_baseEdge_of_kind h h' (by simp [tagKind]))
  · exact iff_of_false (by simp [baseEdgeF]) (not_baseEdge_of_kind h h' (by simp [tagKind]))
  · -- spoke to hub
    change OccDom d s (v c) (v x) at h
    cases b' with
    | true =>
      change IsCl (v c') ∧ v x' = v c' at h'
      change _ ↔ BaseEdge (spk (occOf d s (v c) (v x) h)) (hub (Sum.inl ⟨v c', h'.1⟩))
      rw [baseEdge_spk_hub_iff, hubOf_eq_inl_iff, occOf_c]
      cases d <;> simp [baseEdgeF, occC, realize_eqF]
    | false =>
      change SatOccurs A (v c') ∧ v x' = v c' at h'
      change _ ↔ BaseEdge (spk (occOf d s (v c) (v x) h)) (hub (Sum.inr ⟨v c', h'.1⟩))
      rw [baseEdge_spk_hub_iff, hubOf_eq_inr_iff, occOf_c, occOf_x]
      cases d <;> simp [baseEdgeF, occC, realize_eqF]
  · exact iff_of_false (by simp [baseEdgeF]) (not_baseEdge_of_kind h h' (by simp [tagKind]))
  · -- hub to spoke
    change OccDom d' s' (v c') (v x') at h'
    cases b with
    | true =>
      change IsCl (v c) ∧ v x = v c at h
      change _ ↔ BaseEdge (hub (Sum.inl ⟨v c, h.1⟩)) (spk (occOf d' s' (v c') (v x') h'))
      rw [baseEdge_hub_spk_iff, hubOf_eq_inl_iff, occOf_c]
      cases d' <;> simp [baseEdgeF, occC, realize_eqF, eq_comm]
    | false =>
      change SatOccurs A (v c) ∧ v x = v c at h
      change _ ↔ BaseEdge (hub (Sum.inr ⟨v c, h.1⟩)) (spk (occOf d' s' (v c') (v x') h'))
      rw [baseEdge_hub_spk_iff, hubOf_eq_inr_iff, occOf_c, occOf_x]
      cases d' <;> simp [baseEdgeF, occC, realize_eqF, eq_comm]
  · exact iff_of_false (by simp [baseEdgeF]) (not_baseEdge_of_kind h h' (by simp [tagKind]))

/-! #### The entries of the attached matrix -/

/-- **The attached matrix**: the base matrix with Valiant's gadget attached
at every site, on the flat node type. -/
noncomputable abbrev attachedM : V A → V A → ℤ :=
  Site.flatAttach baseM site

theorem xorGadget_bounds (j j' : Fin 4) : -1 ≤ xorGadget j j' ∧ xorGadget j j' ≤ 3 := by
  revert j j'
  decide

/-- The entries of the attached matrix are between `-1` and `3`. -/
theorem attachedM_bounds (a b : V A) : -1 ≤ attachedM a b ∧ attachedM a b ≤ 3 := by
  rcases a with n | ⟨o, j⟩ <;> rcases b with n' | ⟨o', j'⟩
  · simp only [attachedM, Site.flatAttach, baseM]
    split_ifs <;> omega
  · simp only [attachedM, Site.flatAttach]
    split_ifs <;> omega
  · simp only [attachedM, Site.flatAttach]
    split_ifs <;> omega
  · simp only [attachedM, Site.flatAttach]
    split_ifs
    · exact xorGadget_bounds j j'
    · omega

omit [Fintype A] in
theorem realize_ite_bot {β : Type} {w : β → A} (p : Prop) [Decidable p] (φ : satOrd.Formula β) :
    (if p then φ else ⊥).Realize w ↔ p ∧ φ.Realize w := by
  split_ifs with hp <;> simp [hp]

omit [LinearOrder A] [Fintype A] in
theorem ite_one_eq_iff {k : ℤ} (_hk : k ≠ 0) (P : Prop) [Decidable P] :
    (if P then (1 : ℤ) else 0) = k ↔ k = 1 ∧ P := by
  split_ifs with hp
  · simp [hp, eq_comm]
  · simp [hp]
    omega

omit [LinearOrder A] [Fintype A] in
theorem ite_add_ite_eq_iff {k : ℤ} (_hk : k ≠ 0) (P Q : Prop) [Decidable P] [Decidable Q]
    (hPQ : ¬(P ∧ Q)) :
    ((if P then (1 : ℤ) else 0) + if Q then 1 else 0) = k ↔ k = 1 ∧ (P ∨ Q) := by
  split_ifs with hp hq <;> simp_all <;> omega

omit [LinearOrder A] [Fintype A] in
theorem ite_eq_iff_of_ne {k z : ℤ} (_hk : k ≠ 0) (P : Prop) [Decidable P] :
    (if P then z else 0) = k ↔ P ∧ z = k := by
  split_ifs with hp
  · simp [hp]
  · simp [hp]
    omega

theorem realize_flatEntryF {k : ℤ} (hk : k ≠ 0) {t t' : VTag} {c x c' x' : α}
    (h : VDom t (v c) (v x)) (h' : VDom t' (v c') (v x')) :
    (flatEntryF k t t' c x c' x').Realize v ↔
      attachedM (vOf t (v c) (v x) h) (vOf t' (v c') (v x') h') = k := by
  rcases t with t | ⟨⟨d, s⟩, j⟩ <;> rcases t' with t' | ⟨⟨d', s'⟩, j'⟩
  · -- base to base
    change NodeDom t (v c) (v x) at h
    change NodeDom t' (v c') (v x') at h'
    simp only [flatEntryF, vOf, attachedM, Site.flatAttach, baseM]
    rw [realize_ite_bot, realize_baseEdgeF h h', ite_one_eq_iff hk]
  · -- base to gadget
    change NodeDom t (v c) (v x) at h
    change OccDom d' s' (v c') (v x') at h'
    have h1' : NodeDom (Sum.inl (d', s')) (v c') (v x') := h'
    have h2' : NodeDom (Sum.inr (Sum.inl (d', s'))) (v c') (v x') := h'
    have e1 : nodeOf t (v c) (v x) h = trk (occOf d' s' (v c') (v x') h') ↔
        t = Sum.inl (d', s') ∧ (v c, v x) = (v c', v x') :=
      nodeOf_eq_iff h h1'
    have e2 : nodeOf t (v c) (v x) h = spk (occOf d' s' (v c') (v x') h') ↔
        t = Sum.inr (Sum.inl (d', s')) ∧ (v c, v x) = (v c', v x') :=
      nodeOf_eq_iff h h2'
    have hex : ¬((nodeOf t (v c) (v x) h = (site (occOf d' s' (v c') (v x') h')).u ∧ j' = 0) ∧
        (nodeOf t (v c) (v x) h = (site (occOf d' s' (v c') (v x') h')).u' ∧ j' = 3)) := by
      rintro ⟨⟨_, h0⟩, ⟨_, h3⟩⟩
      rw [h0] at h3
      exact absurd h3 (by decide)
    simp only [flatEntryF, vOf, attachedM, Site.flatAttach]
    rw [realize_ite_bot, ite_add_ite_eq_iff hk _ _ hex]
    change _ ↔ k = 1 ∧ ((nodeOf t (v c) (v x) h = trk (occOf d' s' (v c') (v x') h') ∧ j' = 0) ∨
      (nodeOf t (v c) (v x) h = spk (occOf d' s' (v c') (v x') h') ∧ j' = 3))
    rw [e1, e2, Formula.realize_inf, realize_eqF, realize_eqF, Prod.mk.injEq]
    tauto
  · -- gadget to base
    change OccDom d s (v c) (v x) at h
    change NodeDom t' (v c') (v x') at h'
    have h1' : NodeDom (Sum.inl (d, s)) (v c) (v x) := h
    have h2' : NodeDom (Sum.inr (Sum.inl (d, s))) (v c) (v x) := h
    have e1 : nodeOf t' (v c') (v x') h' = trk (occOf d s (v c) (v x) h) ↔
        t' = Sum.inl (d, s) ∧ (v c', v x') = (v c, v x) :=
      nodeOf_eq_iff h' h1'
    have e2 : nodeOf t' (v c') (v x') h' = spk (occOf d s (v c) (v x) h) ↔
        t' = Sum.inr (Sum.inl (d, s)) ∧ (v c', v x') = (v c, v x) :=
      nodeOf_eq_iff h' h2'
    have hex : ¬((j = 3 ∧ nodeOf t' (v c') (v x') h' = (site (occOf d s (v c) (v x) h)).v) ∧
        (j = 0 ∧ nodeOf t' (v c') (v x') h' = (site (occOf d s (v c) (v x) h)).v')) := by
      rintro ⟨⟨h3, _⟩, ⟨h0, _⟩⟩
      rw [h0] at h3
      exact absurd h3 (by decide)
    simp only [flatEntryF, vOf, attachedM, Site.flatAttach]
    rw [realize_ite_bot, ite_add_ite_eq_iff hk _ _ hex]
    change _ ↔ k = 1 ∧ ((j = 3 ∧ nodeOf t' (v c') (v x') h' = trk (occOf d s (v c) (v x) h)) ∨
      (j = 0 ∧ nodeOf t' (v c') (v x') h' = spk (occOf d s (v c) (v x) h)))
    rw [e1, e2, Formula.realize_inf, realize_eqF, realize_eqF, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hk1, hC⟩, hc, hx⟩
      exact ⟨hk1, hC.imp (fun h => ⟨h.1, h.2, hc.symm, hx.symm⟩)
        fun h => ⟨h.1, h.2, hc.symm, hx.symm⟩⟩
    · rintro ⟨hk1, ⟨hj, ht, hc, hx⟩ | ⟨hj, ht, hc, hx⟩⟩
      · exact ⟨⟨hk1, Or.inl ⟨hj, ht⟩⟩, hc.symm, hx.symm⟩
      · exact ⟨⟨hk1, Or.inr ⟨hj, ht⟩⟩, hc.symm, hx.symm⟩
  · -- gadget to gadget
    change OccDom d s (v c) (v x) at h
    change OccDom d' s' (v c') (v x') at h'
    simp only [flatEntryF, vOf, attachedM, Site.flatAttach]
    rw [realize_ite_bot, ite_eq_iff_of_ne hk, occOf_eq_iff h h', Formula.realize_inf, realize_eqF,
      realize_eqF, Prod.mk.injEq, Prod.mk.injEq]
    tauto

/-! #### The levels -/

/-- The levels of the ladders, as a relativized interpretation into the empty
vocabulary: the number of levels is then a definable cardinality. -/
noncomputable def levelsInterp : RelFOInterpretation satOrd Language.empty LevelTag 2 where
  relFormula := fun R => isEmptyElim R
  domFormula := fun t => levelDomF t 0 1

end Realize

/-- **The levels**: the universe of the interpretation of the levels, ordered
lexicographically. -/
abbrev Level (A : Type) [Language.sat.Structure A] [LinearOrder A] : Type :=
  levelsInterp.MapRel A

section Level

variable {A : Type} [Language.sat.Structure A] [LinearOrder A]

noncomputable instance : LinearOrder (Level A) := levelsInterp.mapRelLinearOrder A

instance [Finite A] : Finite (Level A) := levelsInterp.mapRel_finite A

noncomputable instance [Finite A] : Fintype (Level A) := Fintype.ofFinite _

theorem levelDom_of (ℓ : Level A) : LevelDom ℓ.1.1 (ℓ.1.2 0) (ℓ.1.2 1) :=
  realize_levelDomF.mp ℓ.2

/-- A level, from its tag and its pair. -/
def mkLevel (t : LevelTag) (c x : A) (h : LevelDom t c x) : Level A :=
  ⟨(t, ![c, x]), realize_levelDomF.mpr h⟩

theorem mkLevel_eq (ℓ : Level A) : mkLevel ℓ.1.1 (ℓ.1.2 0) (ℓ.1.2 1) (levelDom_of ℓ) = ℓ :=
  Subtype.ext (Prod.ext rfl (funext fun j => by fin_cases j <;> rfl))

/-- The extra level, for nonempty instances. -/
noncomputable def extraLevel [Fintype A] [Nonempty A] : Level A :=
  mkLevel LevelTag.extra (univ.min' univ_nonempty) (univ.min' univ_nonempty)
    ⟨fun y => min'_le _ _ (mem_univ y), rfl⟩

instance [Finite A] [Nonempty A] : Nonempty (Level A) :=
  letI := Fintype.ofFinite A
  ⟨extraLevel⟩

noncomputable instance [Finite A] [Nonempty A] : BoundedOrder (Level A) :=
  Fintype.toBoundedOrder _

omit [Language.sat.Structure A] in
theorem tupLeLex_two (c x c' x' : A) :
    tupLeLex ![c, x] ![c', x'] ↔ c < c' ∨ (c = c' ∧ x ≤ x') := by
  constructor
  · rintro (h | ⟨j, hj, hlt⟩)
    · have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
      exact Or.inr ⟨h0, h1.le⟩
    · fin_cases j
      · exact Or.inl (by simpa using hlt)
      · refine Or.inr ⟨by simpa using hj 0 (by decide), ?_⟩
        simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one] at hlt
        exact hlt.le
  · rintro (h | ⟨rfl, h⟩)
    · exact Or.inr ⟨0, fun i hi => absurd hi (Fin.not_lt_zero i), by simpa using h⟩
    · rcases h.lt_or_eq with h | rfl
      · refine Or.inr ⟨1, fun i hi => ?_, by simpa using h⟩
        fin_cases i
        · rfl
        · exact absurd hi (by decide)
      · exact Or.inl rfl

/-- The order of the levels, read on the tags and the pairs. -/
theorem mkLevel_le_iff {t t' : LevelTag} {c x c' x' : A} (h : LevelDom t c x)
    (h' : LevelDom t' c' x') :
    mkLevel t c x h ≤ mkLevel t' c' x' h' ↔ t < t' ∨ (t = t' ∧ (c < c' ∨ (c = c' ∧ x ≤ x'))) := by
  change (tagTupleOrder : LinearOrder (LevelTag × (Fin 2 → A))).le (t, ![c, x]) (t', ![c', x']) ↔ _
  rw [← tagTupleLe_iff_le, tagTupleLe, tupLeLex_two]

end Level

/-! ### Realization of the level formulas and of the widths -/

section LevelRealize

variable {A : Type} [Language.sat.Structure A] [LinearOrder A] {α : Type} {v : α → A}

theorem realize_levelLeF {t t' : LevelTag} {c x c' x' : α} (h : LevelDom t (v c) (v x))
    (h' : LevelDom t' (v c') (v x')) :
    (levelLeF t t' c x c' x').Realize v ↔
      mkLevel t (v c) (v x) h ≤ mkLevel t' (v c') (v x') h' := by
  rw [mkLevel_le_iff, levelLeF]
  split_ifs with h1 h2
  · simp only [Formula.realize_top, true_iff]
    exact Or.inl h1
  · simp only [Formula.realize_bot, false_iff]
    rintro (h | ⟨rfl, _⟩)
    · exact h1 h
    · exact lt_irrefl _ h2
  · have ht : t = t' := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
    rw [Formula.realize_sup, Formula.realize_inf, realize_ltF, realize_eqF, realize_leF]
    simp only [ht, lt_self_iff_false, false_or, true_and]

theorem realize_levelLtF {t t' : LevelTag} {c x c' x' : α} (h : LevelDom t (v c) (v x))
    (h' : LevelDom t' (v c') (v x')) :
    (levelLtF t t' c x c' x').Realize v ↔
      mkLevel t (v c) (v x) h < mkLevel t' (v c') (v x') h' := by
  rw [levelLtF, Formula.realize_inf, Formula.realize_not, realize_levelLeF h h',
    realize_levelLeF h' h, lt_iff_le_not_ge]

variable [Finite A] [Nonempty A]

theorem realize_levelMinF {t : LevelTag} {c x : α} (h : LevelDom t (v c) (v x)) :
    (levelMinF t c x).Realize v ↔ mkLevel t (v c) (v x) h = ⊥ := by
  rw [← isBot_iff_eq_bot]
  simp only [levelMinF, Formula.realize_iInf, Formula.realize_iAlls, Formula.realize_imp]
  constructor
  · intro H ℓ
    have hd : LevelDom ℓ.1.1 (ℓ.1.2 0) (ℓ.1.2 1) := levelDom_of ℓ
    have := H ℓ.1.1 ℓ.1.2 (realize_levelDomF.mpr hd)
    rw [realize_levelLeF (v := Sum.elim v ℓ.1.2) (c := Sum.inl c) (x := Sum.inl x)
      (c' := Sum.inr 0) (x' := Sum.inr 1) h hd] at this
    exact mkLevel_eq ℓ ▸ this
  · intro H t' w hw
    rw [realize_levelDomF] at hw
    rw [realize_levelLeF (v := Sum.elim v w) (c := Sum.inl c) (x := Sum.inl x)
      (c' := Sum.inr 0) (x' := Sum.inr 1) h hw]
    exact H _

theorem realize_levelMaxF {t : LevelTag} {c x : α} (h : LevelDom t (v c) (v x)) :
    (levelMaxF t c x).Realize v ↔ mkLevel t (v c) (v x) h = ⊤ := by
  rw [← isTop_iff_eq_top]
  simp only [levelMaxF, Formula.realize_iInf, Formula.realize_iAlls, Formula.realize_imp]
  constructor
  · intro H ℓ
    have hd : LevelDom ℓ.1.1 (ℓ.1.2 0) (ℓ.1.2 1) := levelDom_of ℓ
    have := H ℓ.1.1 ℓ.1.2 (realize_levelDomF.mpr hd)
    rw [realize_levelLeF (v := Sum.elim v ℓ.1.2) (c := Sum.inr 0) (x := Sum.inr 1)
      (c' := Sum.inl c) (x' := Sum.inl x) hd h] at this
    exact mkLevel_eq ℓ ▸ this
  · intro H t' w hw
    rw [realize_levelDomF] at hw
    rw [realize_levelLeF (v := Sum.elim v w) (c := Sum.inr 0) (x := Sum.inr 1)
      (c' := Sum.inl c) (x' := Sum.inl x) hw h]
    exact H _

omit [Finite A] [Nonempty A] in
theorem realize_levelCovF {t t' : LevelTag} {c x c' x' : α} (h : LevelDom t (v c) (v x))
    (h' : LevelDom t' (v c') (v x')) :
    (levelCovF t t' c x c' x').Realize v ↔
      mkLevel t (v c) (v x) h ⋖ mkLevel t' (v c') (v x') h' := by
  simp only [levelCovF, Formula.realize_inf, Formula.realize_not, Formula.realize_iSup,
    Formula.realize_iExs]
  rw [realize_levelLtF h h']
  refine and_congr_right fun _ => ?_
  constructor
  · intro H ℓ hlt hlt'
    refine H ⟨ℓ.1.1, ℓ.1.2, realize_levelDomF.mpr (levelDom_of ℓ), ?_, ?_⟩
    · rw [realize_levelLtF (v := Sum.elim v ℓ.1.2) (c := Sum.inl c) (x := Sum.inl x)
        (c' := Sum.inr 0) (x' := Sum.inr 1) h (levelDom_of ℓ)]
      exact mkLevel_eq ℓ ▸ hlt
    · rw [realize_levelLtF (v := Sum.elim v ℓ.1.2) (c := Sum.inr 0) (x := Sum.inr 1)
        (c' := Sum.inl c') (x' := Sum.inl x') (levelDom_of ℓ) h']
      exact mkLevel_eq ℓ ▸ hlt'
  · rintro H ⟨t'', w, hw, h1, h2⟩
    rw [realize_levelDomF] at hw
    rw [realize_levelLtF (v := Sum.elim v w) (c := Sum.inl c) (x := Sum.inl x)
      (c' := Sum.inr 0) (x' := Sum.inr 1) h hw] at h1
    rw [realize_levelLtF (v := Sum.elim v w) (c := Sum.inr 0) (x := Sum.inr 1)
      (c' := Sum.inl c') (x' := Sum.inl x') hw h'] at h2
    exact H h1 h2

/-- The widths, read on the tags and the pairs. -/
theorem realize_widthF [Fintype A] {t t' : VTag} {l : LevelTag} {j : Fin 3} {c x c' x' c'' x'' : α}
    (h : VDom t (v c) (v x)) (h' : VDom t' (v c') (v x')) (h'' : LevelDom l (v c'') (v x'')) :
    (widthF t t' l j c x c' x' c'' x'').Realize v ↔
      j.val < widths (Λ := Level A) attachedM (vOf t (v c) (v x) h) (vOf t' (v c') (v x') h')
        (mkLevel l (v c'') (v x'') h'') := by
  simp only [widthF, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    realize_flatEntryF (by decide : (-1 : ℤ) ≠ 0) h h',
    realize_flatEntryF (by decide : (1 : ℤ) ≠ 0) h h',
    realize_flatEntryF (by decide : (2 : ℤ) ≠ 0) h h',
    realize_flatEntryF (by decide : (3 : ℤ) ≠ 0) h h',
    realize_levelMinF h'', realize_ite_bot, Formula.realize_top, and_true, widths]
  obtain ⟨hlo, hhi⟩ := attachedM_bounds (vOf t (v c) (v x) h) (vOf t' (v c') (v x') h')
  generalize attachedM (vOf t (v c) (v x) h) (vOf t' (v c') (v x') h') = m at hlo hhi ⊢
  generalize mkLevel l (v c'') (v x'') h'' = ℓ
  by_cases hm : m = -1
  · simp only [hm, ↓reduceIte, true_and, not_true_eq_false, false_and, or_false]
  · simp only [hm, false_and, false_or, not_false_eq_true, true_and]
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨m.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [Int.toNat_natCast]
    by_cases hℓ : ℓ = ⊥
    · simp only [hℓ, ↓reduceIte, true_and, not_true_eq_false, false_and, or_false]
      omega
    · simp only [hℓ, ↓reduceIte, false_and, false_or, not_false_eq_true, true_and]

end LevelRealize

end SatCover

end DescriptiveComplexity
