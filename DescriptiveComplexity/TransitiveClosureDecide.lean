/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.OrderWalk
import DescriptiveComplexity.TransitiveClosurePull

/-!
# Deciders: walks with two exits, closed under the first-order connectives

Immerman's normal form for FO(TC) – a `TC` of a formula containing `TC`s is a
single `TC` – is proved here not as a normal form on formulas but as an
*algebra of walks*. A `DescriptiveComplexity.Decider` is a walk (modes and a
tuple of coordinates, as `DescriptiveComplexity.TCSpec`) with two **exits**,
`yes` and `no`, and a *parameter* type `β` its formulas may mention. It
*decides* a proposition at a valuation of its parameters when, from its start
mode and **any** tuple of coordinates, the `yes` exit is reachable exactly if
the proposition holds and the `no` exit exactly if it fails
(`DescriptiveComplexity.Decider.Decides`).

Starting from any tuple, rather than from a canonical one, is what makes the
constructions below compose without resets: a decider run after another one
simply starts where the previous one exited.

## The algebra

* `DescriptiveComplexity.Decider.atom` decides a first-order formula over the
  base, by exiting at once;
* `DescriptiveComplexity.Decider.neg` swaps the two exits – negation is free,
  the decider being asked for both answers;
* `DescriptiveComplexity.Decider.seq` runs a second decider after the first
  exited `yes` – conjunction;
* `DescriptiveComplexity.Decider.all` runs a decider once per element of the
  universe, in the order of the structure, restarting it after each `yes` and
  exiting `yes` after the last element – universal quantification, with the
  quantified element frozen into a coordinate of the walk;
* `DescriptiveComplexity.Decider.relabelPar` renames the parameters.

Disjunction, implication and the existential quantifier are De Morgan
combinations (`DescriptiveComplexity.Decider.exTup` is an existential over a
whole tuple). What is *not* here is the atom case for a walk's own
reachability relation, which is where nondeterminism (or a step budget) comes
in: `DescriptiveComplexity.TransitiveClosureDecideReach` and
`DescriptiveComplexity.TransitiveClosureDecideReachDet`.

## Determinism travels

Every construction preserves **functionality** – at most one move, step or
exit, out of every node (`DescriptiveComplexity.Decider.Functional`). This is
what makes the same algebra serve the deterministic logic: a functional
decider, turned into a specification (`DescriptiveComplexity.Decider.toSpec`),
is unchanged by determinization.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Copying coordinates -/

section CopyF

variable {L : Language.{0, 0}} {γ ι : Type} [Finite ι]

/-- The formula “the variables `sel'` hold the same values as the variables
`sel`”, coordinate by coordinate. -/
noncomputable def copyF (sel sel' : ι → γ) : L.Formula γ :=
  Formula.iInf fun i => Term.equal (Term.var (sel i)) (Term.var (sel' i))

variable {A : Type} [L.Structure A] {v : γ → A}

@[simp]
theorem realize_copyF (sel sel' : ι → γ) :
    (copyF (L := L) sel sel').Realize v ↔ v ∘ sel' = v ∘ sel := by
  rw [copyF, Formula.realize_iInf]
  simp only [Formula.realize_equal, Term.realize_var]
  exact ⟨fun h => funext fun i => (h i).symm, fun h i => (congrFun h i).symm⟩

end CopyF

/-! ### Paths: an invariant and a lifting -/

section Paths

variable {N : Type} {R : N → N → Prop}

/-- An invariant preserved by every step holds along a path. -/
theorem reach_invariant {P : N → Prop} (hP : ∀ a b, P a → R a b → P b) {a b : N}
    (h : Relation.ReflTransGen R a b) (ha : P a) : P b := by
  induction h with
  | refl => exact ha
  | tail _ hcd ih => exact hP _ _ ih hcd

end Paths

/-! ### Deciders -/

/-- A **decider**: a walk on tuples of `Coord` coordinates carrying a finite
mode, with formulas that may mention parameters of type `β`, and two
*exits* – `yes` (`true`) and `no` (`false`) – each a formula on the current
tuple and the parameters. Its formulas are over the ordered expansion of the
vocabulary, the iteration of `DescriptiveComplexity.Decider.all` needing the
order. -/
structure Decider (L : Language.{0, 0}) (β : Type) : Type 1 where
  /-- The modes. -/
  Mode : Type
  /-- Modes are finite. -/
  [modeFinite : Finite Mode]
  /-- The coordinates of a tuple. -/
  Coord : Type
  /-- Tuples are finite. -/
  [coordFinite : Finite Coord]
  /-- The starting mode. -/
  start : Mode
  /-- The step formula, one per pair of modes: the current tuple, the next
  one, then the parameters. -/
  step : Mode → Mode → (L.sum Language.order).Formula ((Coord ⊕ Coord) ⊕ β)
  /-- The exit formulas: at a mode, the condition on the current tuple and the
  parameters under which the walk exits with the given answer. -/
  exit : Mode → Bool → (L.sum Language.order).Formula (Coord ⊕ β)

attribute [instance] Decider.modeFinite Decider.coordFinite

namespace Decider

section Semantics

variable {L : Language.{0, 0}} {β : Type} (D : Decider L β) {A : Type} [L.Structure A]
  [LinearOrder A]

variable (A) in
/-- A node of the walk: a mode together with a tuple. -/
abbrev Node : Type := D.Mode × (D.Coord → A)

/-- One step of the walk, at a valuation of the parameters. -/
def StepAt (v : β → A) (a b : D.Node A) : Prop :=
  (D.step a.1 b.1).Realize (Sum.elim (Sum.elim a.2 b.2) v)

/-- Reachability in the walk, at a valuation of the parameters. -/
abbrev ReachAt (v : β → A) : D.Node A → D.Node A → Prop :=
  Relation.ReflTransGen (D.StepAt v)

/-- The walk exits at a node with an answer. -/
def ExitAt (v : β → A) (a : D.Node A) (o : Bool) : Prop :=
  (D.exit a.1 o).Realize (Sum.elim a.2 v)

/-- The answer `o` is reachable from the start mode at the tuple `t`. -/
def Out (v : β → A) (t : D.Coord → A) (o : Bool) : Prop :=
  ∃ a, D.ReachAt v (D.start, t) a ∧ D.ExitAt v a o

/-- **The decider decides `P`** at a valuation of its parameters: from the
start mode and any tuple, `yes` is reachable exactly when `P` holds, and `no`
exactly when it fails. -/
def Decides (v : β → A) (P : Prop) : Prop :=
  ∀ t : D.Coord → A, (D.Out v t true ↔ P) ∧ (D.Out v t false ↔ ¬P)

/-- A move out of a node: a step to another node, or an exit. -/
def Move (v : β → A) (a : D.Node A) : D.Node A ⊕ Bool → Prop
  | Sum.inl b => D.StepAt v a b
  | Sum.inr o => D.ExitAt v a o

variable (A) in
/-- A decider is *functional* when no node has two moves: the walk is
deterministic, exits included. -/
def Functional : Prop :=
  ∀ (v : β → A) (a : D.Node A) (m m' : D.Node A ⊕ Bool), D.Move v a m → D.Move v a m' → m = m'

variable {D}

theorem Decides.congr {v : β → A} {P Q : Prop} (h : D.Decides v P) (hPQ : P ↔ Q) :
    D.Decides v Q :=
  fun t => ⟨((h t).1).trans hPQ, ((h t).2).trans (not_congr hPQ)⟩

theorem Decides.congr_val {v w : β → A} {P : Prop} (h : D.Decides v P) (hvw : v = w) :
    D.Decides w P :=
  hvw ▸ h

theorem Functional.step_unique (h : D.Functional A) {v : β → A} {a b c : D.Node A}
    (hb : D.StepAt v a b) (hc : D.StepAt v a c) : b = c :=
  Sum.inl_injective (h v a (Sum.inl b) (Sum.inl c) hb hc)

theorem Functional.not_exit_of_step (h : D.Functional A) {v : β → A} {a b : D.Node A}
    (hb : D.StepAt v a b) {o : Bool} (ho : D.ExitAt v a o) : False :=
  Sum.inl_ne_inr (h v a (Sum.inl b) (Sum.inr o) hb ho)

theorem Functional.exit_unique (h : D.Functional A) {v : β → A} {a : D.Node A} {o o' : Bool}
    (ho : D.ExitAt v a o) (ho' : D.ExitAt v a o') : o = o' :=
  Sum.inr_injective (h v a (Sum.inr o) (Sum.inr o') ho ho')

/-- Functionality, from its three components. -/
theorem functional_of (hstep : ∀ (v : β → A) (a b c : D.Node A),
      D.StepAt v a b → D.StepAt v a c → b = c)
    (hexit : ∀ (v : β → A) (a b : D.Node A) (o : Bool), D.StepAt v a b → ¬D.ExitAt v a o)
    (hboth : ∀ (v : β → A) (a : D.Node A), D.ExitAt v a true → ¬D.ExitAt v a false) :
    D.Functional A := by
  intro v a m m' hm hm'
  rcases m with b | o <;> rcases m' with c | o'
  · exact congrArg Sum.inl (hstep v a b c hm hm')
  · exact absurd hm' (hexit v a b o' hm)
  · exact absurd hm (hexit v a c o hm')
  · cases o <;> cases o'
    · rfl
    · exact absurd hm (hboth v a hm')
    · exact absurd hm' (hboth v a hm)
    · rfl

end Semantics

/-! ### Renaming the parameters -/

section Relabel

variable {L : Language.{0, 0}} {β γ : Type}

/-- The decider with its parameters renamed along `f`: a parameter of the new
decider is read where `f` sends it. -/
@[reducible]
noncomputable def relabelPar (D : Decider L β) (f : β → γ) : Decider L γ where
  Mode := D.Mode
  Coord := D.Coord
  start := D.start
  step m n := (D.step m n).relabel (Sum.map id f)
  exit m o := (D.exit m o).relabel (Sum.map id f)

variable (D : Decider L β) (f : β → γ) {A : Type} [L.Structure A] [LinearOrder A] (v : γ → A)

theorem stepAt_relabelPar (a b : D.Node A) :
    (D.relabelPar f).StepAt v a b ↔ D.StepAt (v ∘ f) a b := by
  change ((D.step a.1 b.1).relabel (Sum.map id f)).Realize (Sum.elim (Sum.elim a.2 b.2) v) ↔
    (D.step a.1 b.1).Realize (Sum.elim (Sum.elim a.2 b.2) (v ∘ f))
  rw [Formula.realize_relabel]
  refine iff_of_eq (congrArg (D.step a.1 b.1).Realize (funext fun i => ?_))
  rcases i with (i | i) | i <;> rfl

theorem exitAt_relabelPar (a : D.Node A) (o : Bool) :
    (D.relabelPar f).ExitAt v a o ↔ D.ExitAt (v ∘ f) a o := by
  change ((D.exit a.1 o).relabel (Sum.map id f)).Realize (Sum.elim a.2 v) ↔
    (D.exit a.1 o).Realize (Sum.elim a.2 (v ∘ f))
  rw [Formula.realize_relabel]
  refine iff_of_eq (congrArg (D.exit a.1 o).Realize (funext fun i => ?_))
  rcases i with i | i <;> rfl

theorem reachAt_relabelPar (a b : D.Node A) :
    (D.relabelPar f).ReachAt v a b ↔ D.ReachAt (v ∘ f) a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih => exact ih.tail ((D.stepAt_relabelPar f v c d).mp hcd)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih => exact ih.tail ((D.stepAt_relabelPar f v c d).mpr hcd)

theorem out_relabelPar (t : D.Coord → A) (o : Bool) :
    (D.relabelPar f).Out v t o ↔ D.Out (v ∘ f) t o :=
  exists_congr fun a => and_congr (D.reachAt_relabelPar f v _ a) (D.exitAt_relabelPar f v a o)

theorem decides_relabelPar {P : Prop} (h : D.Decides (v ∘ f) P) : (D.relabelPar f).Decides v P :=
  fun t => ⟨(D.out_relabelPar f v t true).trans (h t).1,
    (D.out_relabelPar f v t false).trans (h t).2⟩

theorem functional_relabelPar (h : D.Functional A) : (D.relabelPar f).Functional A := by
  intro v a m m' hm hm'
  refine h (v ∘ f) a m m' ?_ ?_
  · rcases m with b | o
    · exact (D.stepAt_relabelPar f v a b).mp hm
    · exact (D.exitAt_relabelPar f v a o).mp hm
  · rcases m' with b | o
    · exact (D.stepAt_relabelPar f v a b).mp hm'
    · exact (D.exitAt_relabelPar f v a o).mp hm'

end Relabel

/-! ### Atoms -/

section Atom

variable {L : Language.{0, 0}} {β : Type}

/-- The decider of a first-order formula over the base: no step, and it exits
at once with the truth value of the formula. -/
@[reducible]
noncomputable def atom (ψ : (L.sum Language.order).Formula β) : Decider L β where
  Mode := Unit
  Coord := Empty
  start := ()
  step _ _ := ⊥
  exit _ o := if o then ψ.relabel Sum.inr else ∼(ψ.relabel Sum.inr)

variable (ψ : (L.sum Language.order).Formula β) {A : Type} [L.Structure A] [LinearOrder A]
  (v : β → A)

theorem exitAt_atom (a : (atom ψ).Node A) (o : Bool) :
    (atom ψ).ExitAt v a o ↔ (if o then ψ.Realize v else ¬ψ.Realize v) := by
  cases o
  · change Formula.Realize (∼(ψ.relabel Sum.inr)) (Sum.elim a.2 v) ↔ ¬ψ.Realize v
    rw [Formula.realize_not, Formula.realize_relabel]
    exact not_congr (iff_of_eq (congrArg ψ.Realize (funext fun i => rfl)))
  · change (ψ.relabel Sum.inr).Realize (Sum.elim a.2 v) ↔ ψ.Realize v
    rw [Formula.realize_relabel]
    exact iff_of_eq (congrArg ψ.Realize (funext fun i => rfl))

theorem not_stepAt_atom (a b : (atom ψ).Node A) : ¬(atom ψ).StepAt v a b :=
  fun h => h

theorem reachAt_atom {a b : (atom ψ).Node A} (h : (atom ψ).ReachAt v a b) : b = a := by
  induction h with
  | refl => rfl
  | tail _ hcd _ => exact absurd hcd (not_stepAt_atom ψ v _ _)

theorem decides_atom : (atom ψ).Decides v (ψ.Realize v) := by
  intro t
  have hout : ∀ o, (atom ψ).Out v t o ↔ (if o then ψ.Realize v else ¬ψ.Realize v) := by
    intro o
    constructor
    · rintro ⟨a, ha, he⟩
      rw [reachAt_atom ψ v ha] at he
      exact (exitAt_atom ψ v _ o).mp he
    · intro h
      exact ⟨_, Relation.ReflTransGen.refl, (exitAt_atom ψ v _ o).mpr h⟩
  exact ⟨hout true, hout false⟩

theorem functional_atom : (atom ψ).Functional A := by
  refine functional_of (fun v a b c hb _ => absurd hb (not_stepAt_atom ψ v a b))
    (fun v a b o hb _ => absurd hb (not_stepAt_atom ψ v a b)) fun v a h h' => ?_
  rw [exitAt_atom] at h h'
  exact h' h

end Atom

/-! ### Negation -/

section Neg

variable {L : Language.{0, 0}} {β : Type}

/-- The decider with its two exits swapped. -/
@[reducible]
noncomputable def neg (D : Decider L β) : Decider L β where
  Mode := D.Mode
  Coord := D.Coord
  start := D.start
  step := D.step
  exit m o := D.exit m (!o)

variable (D : Decider L β) {A : Type} [L.Structure A] [LinearOrder A] (v : β → A)

theorem stepAt_neg (a b : D.Node A) : D.neg.StepAt v a b ↔ D.StepAt v a b := Iff.rfl

theorem exitAt_neg (a : D.Node A) (o : Bool) : D.neg.ExitAt v a o ↔ D.ExitAt v a (!o) := Iff.rfl

theorem reachAt_neg (a b : D.Node A) : D.neg.ReachAt v a b ↔ D.ReachAt v a b := Iff.rfl

theorem out_neg (t : D.Coord → A) (o : Bool) : D.neg.Out v t o ↔ D.Out v t (!o) := Iff.rfl

theorem decides_neg {P : Prop} (h : D.Decides v P) : D.neg.Decides v (¬P) := by
  intro t
  refine ⟨(D.out_neg v t true).trans (h t).2, (D.out_neg v t false).trans ?_⟩
  rw [not_not]
  exact (h t).1

theorem functional_neg (h : D.Functional A) : D.neg.Functional A := by
  refine functional_of (fun v a b c hb hc => h.step_unique hb hc)
    (fun v a b o hb ho => h.not_exit_of_step ((D.stepAt_neg v a b).mp hb)
      ((D.exitAt_neg v a o).mp ho)) fun v a h₁ h₂ => ?_
  exact Bool.false_ne_true (h.exit_unique ((D.exitAt_neg v a true).mp h₁)
    ((D.exitAt_neg v a false).mp h₂))

end Neg

/-! ### Sequential composition -/

section Seq

variable {L : Language.{0, 0}} {β : Type}

/-- The variables of the first component's step, in the composite's. -/
def seqVarL {C₁ C₂ : Type} : (C₁ ⊕ C₁) ⊕ β → ((C₁ ⊕ C₂) ⊕ (C₁ ⊕ C₂)) ⊕ β :=
  Sum.map (Sum.map Sum.inl Sum.inl) id

/-- The variables of the second component's step, in the composite's. -/
def seqVarR {C₁ C₂ : Type} : (C₂ ⊕ C₂) ⊕ β → ((C₁ ⊕ C₂) ⊕ (C₁ ⊕ C₂)) ⊕ β :=
  Sum.map (Sum.map Sum.inr Sum.inr) id

/-- The variables of the first component's exit, in the composite's exit. -/
def seqExitL {C₁ C₂ : Type} : C₁ ⊕ β → (C₁ ⊕ C₂) ⊕ β := Sum.map Sum.inl id

/-- The variables of the second component's exit, in the composite's exit. -/
def seqExitR {C₁ C₂ : Type} : C₂ ⊕ β → (C₁ ⊕ C₂) ⊕ β := Sum.map Sum.inr id

/-- The variables of the first component's exit, in the composite's step (read
on the current tuple). -/
def seqExitStep {C₁ C₂ : Type} : C₁ ⊕ β → ((C₁ ⊕ C₂) ⊕ (C₁ ⊕ C₂)) ⊕ β :=
  Sum.map (fun c => Sum.inl (Sum.inl c)) id

/-- The current tuple's coordinate `c`, as a step variable. -/
abbrev curVar {C : Type} (c : C) : (C ⊕ C) ⊕ β := Sum.inl (Sum.inl c)

/-- The next tuple's coordinate `c`, as a step variable. -/
abbrev nextVar {C : Type} (c : C) : (C ⊕ C) ⊕ β := Sum.inl (Sum.inr c)

open Classical in
/-- **Sequential composition**: the first decider runs, and where it exits
`yes` the second one starts, from the tuple it left; the answer is the
second's. The coordinates of the idle component are copied along. -/
@[reducible]
noncomputable def seq (D₁ D₂ : Decider L β) : Decider L β where
  Mode := D₁.Mode ⊕ D₂.Mode
  Coord := D₁.Coord ⊕ D₂.Coord
  start := Sum.inl D₁.start
  step m n :=
    match m, n with
    | Sum.inl m, Sum.inl n =>
        (D₁.step m n).relabel seqVarL ⊓
          copyF (fun c : D₂.Coord => curVar (Sum.inr c)) fun c => nextVar (Sum.inr c)
    | Sum.inl m, Sum.inr n =>
        if n = D₂.start then
          (D₁.exit m true).relabel seqExitStep ⊓
            copyF (fun c : D₁.Coord ⊕ D₂.Coord => curVar c) fun c => nextVar c
        else ⊥
    | Sum.inr _, Sum.inl _ => ⊥
    | Sum.inr m, Sum.inr n =>
        (D₂.step m n).relabel seqVarR ⊓
          copyF (fun c : D₁.Coord => curVar (Sum.inl c)) fun c => nextVar (Sum.inl c)
  exit m o :=
    match m with
    | Sum.inl m => if o then ⊥ else (D₁.exit m false).relabel seqExitL
    | Sum.inr m => (D₂.exit m o).relabel seqExitR

variable (D₁ D₂ : Decider L β) {A : Type} [L.Structure A] [LinearOrder A] (v : β → A)

theorem stepAt_seq_inl_inl (m m' : D₁.Mode) (t t' : D₁.Coord ⊕ D₂.Coord → A) :
    (seq D₁ D₂).StepAt v (Sum.inl m, t) (Sum.inl m', t') ↔
      D₁.StepAt v (m, t ∘ Sum.inl) (m', t' ∘ Sum.inl) ∧ t' ∘ Sum.inr = t ∘ Sum.inr := by
  change ((D₁.step m m').relabel seqVarL ⊓ _).Realize _ ↔ _
  rw [Formula.realize_inf, Formula.realize_relabel, realize_copyF]
  refine and_congr (iff_of_eq (congrArg (D₁.step m m').Realize (funext fun i => ?_))) Iff.rfl
  rcases i with (i | i) | i <;> rfl

theorem stepAt_seq_inl_inr (m : D₁.Mode) (m' : D₂.Mode) (t t' : D₁.Coord ⊕ D₂.Coord → A) :
    (seq D₁ D₂).StepAt v (Sum.inl m, t) (Sum.inr m', t') ↔
      m' = D₂.start ∧ D₁.ExitAt v (m, t ∘ Sum.inl) true ∧ t' = t := by
  classical
  have hstep : (seq D₁ D₂).step (Sum.inl m) (Sum.inr m') = if m' = D₂.start then
      (D₁.exit m true).relabel seqExitStep ⊓
        copyF (fun c : D₁.Coord ⊕ D₂.Coord => curVar c) (fun c => nextVar c)
      else ⊥ := rfl
  unfold StepAt
  rw [hstep]
  split_ifs with h
  · rw [Formula.realize_inf, Formula.realize_relabel, realize_copyF, and_iff_right h]
    refine and_congr (iff_of_eq (congrArg (Formula.Realize (M := A) (D₁.exit m true))
      (funext fun i => ?_))) ?_
    · rcases i with i | i <;> rfl
    · exact ⟨fun h => funext fun c => congrFun h c, fun h => funext fun c => congrFun h c⟩
  · simp only [Formula.realize_bot, false_iff, not_and]
    exact fun h' => absurd h' h

theorem not_stepAt_seq_inr_inl (m : D₂.Mode) (m' : D₁.Mode) (t t' : D₁.Coord ⊕ D₂.Coord → A) :
    ¬(seq D₁ D₂).StepAt v (Sum.inr m, t) (Sum.inl m', t') :=
  fun h => h

theorem stepAt_seq_inr_inr (m m' : D₂.Mode) (t t' : D₁.Coord ⊕ D₂.Coord → A) :
    (seq D₁ D₂).StepAt v (Sum.inr m, t) (Sum.inr m', t') ↔
      D₂.StepAt v (m, t ∘ Sum.inr) (m', t' ∘ Sum.inr) ∧ t' ∘ Sum.inl = t ∘ Sum.inl := by
  change ((D₂.step m m').relabel seqVarR ⊓ _).Realize _ ↔ _
  rw [Formula.realize_inf, Formula.realize_relabel, realize_copyF]
  refine and_congr (iff_of_eq (congrArg (D₂.step m m').Realize (funext fun i => ?_))) Iff.rfl
  rcases i with (i | i) | i <;> rfl

theorem exitAt_seq_inl (m : D₁.Mode) (t : D₁.Coord ⊕ D₂.Coord → A) (o : Bool) :
    (seq D₁ D₂).ExitAt v (Sum.inl m, t) o ↔ o = false ∧ D₁.ExitAt v (m, t ∘ Sum.inl) false := by
  cases o
  · change ((D₁.exit m false).relabel seqExitL).Realize _ ↔ _
    rw [Formula.realize_relabel]
    refine (iff_of_eq (congrArg (D₁.exit m false).Realize (funext fun i => ?_))).trans
      (and_iff_right rfl).symm
    rcases i with i | i <;> rfl
  · change (⊥ : (L.sum Language.order).Formula _).Realize _ ↔ _
    simp

theorem exitAt_seq_inr (m : D₂.Mode) (t : D₁.Coord ⊕ D₂.Coord → A) (o : Bool) :
    (seq D₁ D₂).ExitAt v (Sum.inr m, t) o ↔ D₂.ExitAt v (m, t ∘ Sum.inr) o := by
  change ((D₂.exit m o).relabel seqExitR).Realize _ ↔ _
  rw [Formula.realize_relabel]
  refine iff_of_eq (congrArg (D₂.exit m o).Realize (funext fun i => ?_))
  rcases i with i | i <;> rfl

/-- A path of the first component lifts to the composite, the second
component's coordinates fixed. -/
theorem reachAt_seq_of_reachAt₁ {a b : D₁.Node A} (h : D₁.ReachAt v a b) (y : D₂.Coord → A) :
    (seq D₁ D₂).ReachAt v (Sum.inl a.1, Sum.elim a.2 y) (Sum.inl b.1, Sum.elim b.2 y) := by
  refine Relation.ReflTransGen.lift (fun c : D₁.Node A => (Sum.inl c.1, Sum.elim c.2 y))
    (fun c d hcd => ?_) _ _ h
  exact (stepAt_seq_inl_inl D₁ D₂ v c.1 d.1 _ _).mpr (by simpa using hcd)

/-- A path of the second component lifts to the composite, the first
component's coordinates fixed. -/
theorem reachAt_seq_of_reachAt₂ {a b : D₂.Node A} (h : D₂.ReachAt v a b) (x : D₁.Coord → A) :
    (seq D₁ D₂).ReachAt v (Sum.inr a.1, Sum.elim x a.2) (Sum.inr b.1, Sum.elim x b.2) := by
  refine Relation.ReflTransGen.lift (fun c : D₂.Node A => (Sum.inr c.1, Sum.elim x c.2))
    (fun c d hcd => ?_) _ _ h
  exact (stepAt_seq_inr_inr D₁ D₂ v c.1 d.1 _ _).mpr (by simpa using hcd)

/-- What the composite may have reached from its start at `t`: a node of the
first component reached by it, the second's coordinates untouched, or a node of
the second component reached after the first exited `yes`. -/
def SeqInv (t : D₁.Coord ⊕ D₂.Coord → A) (c : (seq D₁ D₂).Node A) : Prop :=
  (∃ (m : D₁.Mode) (t' : D₁.Coord ⊕ D₂.Coord → A), c = (Sum.inl m, t') ∧
      D₁.ReachAt v (D₁.start, t ∘ Sum.inl) (m, t' ∘ Sum.inl) ∧ t' ∘ Sum.inr = t ∘ Sum.inr) ∨
    (∃ (m : D₂.Mode) (t' : D₁.Coord ⊕ D₂.Coord → A), c = (Sum.inr m, t') ∧
      D₁.Out v (t ∘ Sum.inl) true ∧ D₂.ReachAt v (D₂.start, t ∘ Sum.inr) (m, t' ∘ Sum.inr))

theorem seqInv_of_reachAt (t : D₁.Coord ⊕ D₂.Coord → A) {c : (seq D₁ D₂).Node A}
    (h : (seq D₁ D₂).ReachAt v (Sum.inl D₁.start, t) c) : SeqInv D₁ D₂ v t c := by
  refine reach_invariant (P := SeqInv D₁ D₂ v t) (fun a b ha hab => ?_) h
    (Or.inl ⟨D₁.start, t, rfl, Relation.ReflTransGen.refl, rfl⟩)
  obtain ⟨mb, tb⟩ := b
  rcases ha with ⟨m, t', rfl, hr, ht⟩ | ⟨m, t', rfl, ho, hr⟩
  · rcases mb with mb | mb
    · obtain ⟨hs, hc⟩ := (stepAt_seq_inl_inl D₁ D₂ v m mb t' tb).mp hab
      exact Or.inl ⟨mb, tb, rfl, hr.tail hs, hc.trans ht⟩
    · obtain ⟨rfl, he, htb⟩ := (stepAt_seq_inl_inr D₁ D₂ v m mb t' tb).mp hab
      refine Or.inr ⟨D₂.start, tb, rfl, ⟨_, hr, he⟩, ?_⟩
      rw [htb, ht]
  · rcases mb with mb | mb
    · exact absurd hab (not_stepAt_seq_inr_inl D₁ D₂ v m mb t' tb)
    · obtain ⟨hs, -⟩ := (stepAt_seq_inr_inr D₁ D₂ v m mb t' tb).mp hab
      exact Or.inr ⟨mb, tb, rfl, ho, hr.tail hs⟩

theorem out_seq (t : D₁.Coord ⊕ D₂.Coord → A) (o : Bool) :
    (seq D₁ D₂).Out v t o ↔
      (o = false ∧ D₁.Out v (t ∘ Sum.inl) false) ∨
        (D₁.Out v (t ∘ Sum.inl) true ∧ D₂.Out v (t ∘ Sum.inr) o) := by
  constructor
  · rintro ⟨c, hc, he⟩
    rcases seqInv_of_reachAt D₁ D₂ v t hc with ⟨m, t', rfl, hr, -⟩ | ⟨m, t', rfl, ho, hr⟩
    · obtain ⟨rfl, he'⟩ := (exitAt_seq_inl D₁ D₂ v m t' o).mp he
      exact Or.inl ⟨rfl, _, hr, he'⟩
    · exact Or.inr ⟨ho, _, hr, (exitAt_seq_inr D₁ D₂ v m t' o).mp he⟩
  · rintro (⟨rfl, a, ha, he⟩ | ⟨⟨a, ha, he⟩, b, hb, he'⟩)
    · refine ⟨(Sum.inl a.1, Sum.elim a.2 (t ∘ Sum.inr)), ?_, ?_⟩
      · have := reachAt_seq_of_reachAt₁ D₁ D₂ v ha (t ∘ Sum.inr)
        rwa [Sum.elim_comp_inl_inr] at this
      · exact (exitAt_seq_inl D₁ D₂ v a.1 _ false).mpr ⟨rfl, by simpa using he⟩
    · refine ⟨(Sum.inr b.1, Sum.elim a.2 b.2), ?_, (exitAt_seq_inr D₁ D₂ v b.1 _ o).mpr
        (by simpa using he')⟩
      have h1 := reachAt_seq_of_reachAt₁ D₁ D₂ v ha (t ∘ Sum.inr)
      rw [Sum.elim_comp_inl_inr] at h1
      have h2 : (seq D₁ D₂).StepAt v (Sum.inl a.1, Sum.elim a.2 (t ∘ Sum.inr))
          (Sum.inr D₂.start, Sum.elim a.2 (t ∘ Sum.inr)) :=
        (stepAt_seq_inl_inr D₁ D₂ v a.1 D₂.start _ _).mpr ⟨rfl, by simpa using he, rfl⟩
      exact (h1.tail h2).trans (reachAt_seq_of_reachAt₂ D₁ D₂ v hb a.2)

theorem decides_seq {P Q : Prop} (h₁ : D₁.Decides v P) (h₂ : D₂.Decides v Q) :
    (seq D₁ D₂).Decides v (P ∧ Q) := by
  intro t
  rw [out_seq, out_seq, (h₁ _).1, (h₁ _).2, (h₂ _).1, (h₂ _).2]
  constructor
  · simp
  · constructor
    · rintro (⟨-, h⟩ | ⟨hp, hq⟩)
      · exact fun h' => h h'.1
      · exact fun h' => hq h'.2
    · intro h
      by_cases hp : P
      · exact Or.inr ⟨hp, fun hq => h ⟨hp, hq⟩⟩
      · exact Or.inl ⟨rfl, hp⟩

theorem functional_seq (h₁ : D₁.Functional A) (h₂ : D₂.Functional A) :
    (seq D₁ D₂).Functional A := by
  refine functional_of ?_ ?_ ?_
  · rintro v ⟨m, t⟩ ⟨mb, tb⟩ ⟨mc, tc⟩ hb hc
    rcases m with m | m <;> rcases mb with mb | mb <;> rcases mc with mc | mc
    · obtain ⟨hb, hb'⟩ := (stepAt_seq_inl_inl D₁ D₂ v m mb t tb).mp hb
      obtain ⟨hc, hc'⟩ := (stepAt_seq_inl_inl D₁ D₂ v m mc t tc).mp hc
      have := h₁.step_unique hb hc
      refine Prod.ext (congrArg Sum.inl (congrArg Prod.fst this)) (funext fun i => ?_)
      rcases i with i | i
      · exact congrFun (congrArg Prod.snd this) i
      · exact (congrFun hb' i).trans (congrFun hc' i).symm
    · obtain ⟨hb, -⟩ := (stepAt_seq_inl_inl D₁ D₂ v m mb t tb).mp hb
      obtain ⟨-, hc, -⟩ := (stepAt_seq_inl_inr D₁ D₂ v m mc t tc).mp hc
      exact absurd hc (h₁.not_exit_of_step hb)
    · obtain ⟨-, hb, -⟩ := (stepAt_seq_inl_inr D₁ D₂ v m mb t tb).mp hb
      obtain ⟨hc, -⟩ := (stepAt_seq_inl_inl D₁ D₂ v m mc t tc).mp hc
      exact absurd hb (h₁.not_exit_of_step hc)
    · obtain ⟨hmb, -, htb⟩ := (stepAt_seq_inl_inr D₁ D₂ v m mb t tb).mp hb
      obtain ⟨hmc, -, htc⟩ := (stepAt_seq_inl_inr D₁ D₂ v m mc t tc).mp hc
      rw [hmb, hmc, htb, htc]
    · exact absurd hb (not_stepAt_seq_inr_inl D₁ D₂ v m mb t tb)
    · exact absurd hb (not_stepAt_seq_inr_inl D₁ D₂ v m mb t tb)
    · exact absurd hc (not_stepAt_seq_inr_inl D₁ D₂ v m mc t tc)
    · obtain ⟨hb, hb'⟩ := (stepAt_seq_inr_inr D₁ D₂ v m mb t tb).mp hb
      obtain ⟨hc, hc'⟩ := (stepAt_seq_inr_inr D₁ D₂ v m mc t tc).mp hc
      have := h₂.step_unique hb hc
      refine Prod.ext (congrArg Sum.inr (congrArg Prod.fst this)) (funext fun i => ?_)
      rcases i with i | i
      · exact (congrFun hb' i).trans (congrFun hc' i).symm
      · exact congrFun (congrArg Prod.snd this) i
  · rintro v ⟨m, t⟩ ⟨mb, tb⟩ o hb he
    rcases m with m | m <;> rcases mb with mb | mb
    · obtain ⟨hb, -⟩ := (stepAt_seq_inl_inl D₁ D₂ v m mb t tb).mp hb
      obtain ⟨-, he⟩ := (exitAt_seq_inl D₁ D₂ v m t o).mp he
      exact h₁.not_exit_of_step hb he
    · obtain ⟨-, hb, -⟩ := (stepAt_seq_inl_inr D₁ D₂ v m mb t tb).mp hb
      obtain ⟨-, he⟩ := (exitAt_seq_inl D₁ D₂ v m t o).mp he
      exact Bool.noConfusion (h₁.exit_unique hb he)
    · exact not_stepAt_seq_inr_inl D₁ D₂ v m mb t tb hb
    · obtain ⟨hb, -⟩ := (stepAt_seq_inr_inr D₁ D₂ v m mb t tb).mp hb
      exact h₂.not_exit_of_step hb ((exitAt_seq_inr D₁ D₂ v m t o).mp he)
  · rintro v ⟨m, t⟩ h h'
    rcases m with m | m
    · exact Bool.noConfusion ((exitAt_seq_inl D₁ D₂ v m t true).mp h).1
    · exact Bool.noConfusion (h₂.exit_unique ((exitAt_seq_inr D₁ D₂ v m t true).mp h)
        ((exitAt_seq_inr D₁ D₂ v m t false).mp h'))

end Seq

/-! ### Universal quantification: an iteration along the order -/

section All

variable {L : Language.{0, 0}} {β : Type}

/-- The variables of the component's step in the iteration's: the quantified
parameter is read off the current tuple's extra coordinate. -/
def allVar {C : Type} : (C ⊕ C) ⊕ (β ⊕ Unit) → ((C ⊕ Unit) ⊕ (C ⊕ Unit)) ⊕ β
  | Sum.inl (Sum.inl c) => Sum.inl (Sum.inl (Sum.inl c))
  | Sum.inl (Sum.inr c) => Sum.inl (Sum.inr (Sum.inl c))
  | Sum.inr (Sum.inl b) => Sum.inr b
  | Sum.inr (Sum.inr ()) => Sum.inl (Sum.inl (Sum.inr ()))

/-- The variables of the component's exit in the iteration's step (read on the
current tuple). -/
def allExitStep {C : Type} : C ⊕ (β ⊕ Unit) → ((C ⊕ Unit) ⊕ (C ⊕ Unit)) ⊕ β
  | Sum.inl c => Sum.inl (Sum.inl (Sum.inl c))
  | Sum.inr (Sum.inl b) => Sum.inr b
  | Sum.inr (Sum.inr ()) => Sum.inl (Sum.inl (Sum.inr ()))

/-- The variables of the component's exit in the iteration's exit. -/
def allExit {C : Type} : C ⊕ (β ⊕ Unit) → (C ⊕ Unit) ⊕ β
  | Sum.inl c => Sum.inl (Sum.inl c)
  | Sum.inr (Sum.inl b) => Sum.inr b
  | Sum.inr (Sum.inr ()) => Sum.inl (Sum.inr ())

/-- The extra coordinate holding the quantified element, in a step. -/
abbrev yCur {C : Type} : ((C ⊕ Unit) ⊕ (C ⊕ Unit)) ⊕ β := Sum.inl (Sum.inl (Sum.inr ()))

@[inherit_doc yCur]
abbrev yNext {C : Type} : ((C ⊕ Unit) ⊕ (C ⊕ Unit)) ⊕ β := Sum.inl (Sum.inr (Sum.inr ()))

open Classical in
/-- **Universal quantification**: the component is run once per element of
the universe, in the order of the structure, the element being held in one
extra coordinate. The first step sets it to the minimum; where the component
exits `yes` below the maximum, it is restarted at the successor; a `yes` at the
maximum, or a `no` anywhere, is the answer. -/
@[reducible]
noncomputable def all (D : Decider L (β ⊕ Unit)) : Decider L β where
  Mode := Option D.Mode
  Coord := D.Coord ⊕ Unit
  start := none
  step m n :=
    match m, n with
    | none, some n =>
        if n = D.start then
          copyF (fun c : D.Coord => curVar (Sum.inl c)) (fun c => nextVar (Sum.inl c)) ⊓
            minF yNext
        else ⊥
    | none, none => ⊥
    | some _, none => ⊥
    | some m, some n =>
        ((D.step m n).relabel allVar ⊓ copyF (fun _ : Unit => yCur) fun _ => yNext) ⊔
          (if n = D.start then
            (D.exit m true).relabel allExitStep ⊓ succF yCur yNext ⊓
              copyF (fun c : D.Coord => curVar (Sum.inl c)) (fun c => nextVar (Sum.inl c))
          else ⊥)
  exit m o :=
    match m with
    | none => ⊥
    | some m =>
        if o then (D.exit m true).relabel allExit ⊓ maxF (Sum.inl (Sum.inr ()))
        else (D.exit m false).relabel allExit

variable (D : Decider L (β ⊕ Unit)) {A : Type} [L.Structure A] [LinearOrder A] (v : β → A)

/-- The valuation of the component's parameters: the iteration's, and the
current element. -/
abbrev vy (y : A) : β ⊕ Unit → A := Sum.elim v fun _ => y

theorem stepAt_all_none_some (n : D.Mode) (t t' : D.Coord ⊕ Unit → A) :
    D.all.StepAt v (none, t) (some n, t') ↔
      n = D.start ∧ t' ∘ Sum.inl = t ∘ Sum.inl ∧ ∀ a : A, t' (Sum.inr ()) ≤ a := by
  classical
  have hstep : D.all.step none (some n) = if n = D.start then
      copyF (fun c : D.Coord => curVar (Sum.inl c)) (fun c => nextVar (Sum.inl c)) ⊓ minF yNext
      else ⊥ := rfl
  unfold StepAt
  rw [hstep]
  split_ifs with h
  · rw [Formula.realize_inf, realize_copyF, realize_minF, and_iff_right h]
    exact and_congr ⟨fun h => funext fun c => congrFun h c, fun h => funext fun c => congrFun h c⟩
      Iff.rfl
  · simp only [Formula.realize_bot, false_iff, not_and]
    exact fun h' => absurd h' h

theorem not_stepAt_all_none_none (t t' : D.Coord ⊕ Unit → A) :
    ¬D.all.StepAt v (none, t) (none, t') :=
  fun h => h

theorem not_stepAt_all_some_none (m : D.Mode) (t t' : D.Coord ⊕ Unit → A) :
    ¬D.all.StepAt v (some m, t) (none, t') :=
  fun h => h

theorem stepAt_all_some_some (m n : D.Mode) (t t' : D.Coord ⊕ Unit → A) :
    D.all.StepAt v (some m, t) (some n, t') ↔
      (D.StepAt (vy v (t (Sum.inr ()))) (m, t ∘ Sum.inl) (n, t' ∘ Sum.inl) ∧
          t' (Sum.inr ()) = t (Sum.inr ())) ∨
        (n = D.start ∧ D.ExitAt (vy v (t (Sum.inr ()))) (m, t ∘ Sum.inl) true ∧
          (t (Sum.inr ()) < t' (Sum.inr ()) ∧
            ∀ a : A, ¬(t (Sum.inr ()) < a ∧ a < t' (Sum.inr ()))) ∧
          t' ∘ Sum.inl = t ∘ Sum.inl) := by
  classical
  have hstep : D.all.step (some m) (some n) =
      ((D.step m n).relabel allVar ⊓ copyF (fun _ : Unit => yCur) fun _ => yNext) ⊔
        (if n = D.start then
          (D.exit m true).relabel allExitStep ⊓ succF yCur yNext ⊓
            copyF (fun c : D.Coord => curVar (Sum.inl c)) (fun c => nextVar (Sum.inl c))
        else ⊥) := rfl
  unfold StepAt
  rw [hstep, Formula.realize_sup, Formula.realize_inf, Formula.realize_relabel, realize_copyF]
  refine or_congr (and_congr (iff_of_eq (congrArg (Formula.Realize (M := A) (D.step m n))
    (funext fun i => ?_))) ?_) ?_
  · rcases i with (i | i) | (i | ⟨⟩) <;> rfl
  · exact ⟨fun h => congrFun h (), fun h => funext fun _ => h⟩
  · split_ifs with h
    · rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_relabel, realize_succF,
        realize_copyF, and_iff_right h, and_assoc]
      refine and_congr (iff_of_eq (congrArg (Formula.Realize (M := A) (D.exit m true))
        (funext fun i => ?_))) (and_congr Iff.rfl ?_)
      · rcases i with i | (i | ⟨⟩) <;> rfl
      · exact ⟨fun h => funext fun c => congrFun h c, fun h => funext fun c => congrFun h c⟩
    · simp only [Formula.realize_bot, false_iff, not_and]
      exact fun h' => absurd h' h

theorem not_exitAt_all_none (t : D.Coord ⊕ Unit → A) (o : Bool) :
    ¬D.all.ExitAt v (none, t) o :=
  fun h => h

theorem exitAt_all_some (m : D.Mode) (t : D.Coord ⊕ Unit → A) (o : Bool) :
    D.all.ExitAt v (some m, t) o ↔
      D.ExitAt (vy v (t (Sum.inr ()))) (m, t ∘ Sum.inl) o ∧
        (o = true → ∀ a : A, a ≤ t (Sum.inr ())) := by
  have hrel : ∀ o, ((D.exit m o).relabel allExit).Realize (Sum.elim t v) ↔
      D.ExitAt (vy v (t (Sum.inr ()))) (m, t ∘ Sum.inl) o := by
    intro o
    rw [Formula.realize_relabel]
    refine iff_of_eq (congrArg (Formula.Realize (M := A) (D.exit m o)) (funext fun i => ?_))
    rcases i with i | (i | ⟨⟩) <;> rfl
  cases o
  · change ((D.exit m false).relabel allExit).Realize (Sum.elim t v) ↔ _
    rw [hrel]
    exact (and_iff_left fun h => Bool.noConfusion h).symm
  · change ((D.exit m true).relabel allExit ⊓ maxF (Sum.inl (Sum.inr ()))).Realize
      (Sum.elim t v) ↔ _
    rw [Formula.realize_inf, hrel, realize_maxF]
    exact and_congr Iff.rfl ⟨fun h _ => h, fun h => h rfl⟩

/-- A path of the component lifts to the iteration, the element fixed. -/
theorem reachAt_all_of_reachAt {y : A} {a b : D.Node A} (h : D.ReachAt (vy v y) a b) :
    D.all.ReachAt v (some a.1, Sum.elim a.2 fun _ => y) (some b.1, Sum.elim b.2 fun _ => y) := by
  refine Relation.ReflTransGen.lift
    (fun c : D.Node A => (some c.1, Sum.elim c.2 fun _ => y)) (fun c d hcd => ?_) _ _ h
  exact (stepAt_all_some_some D v c.1 d.1 _ _).mpr (Or.inl ⟨by simpa using hcd, rfl⟩)

variable [Finite A]

/-- **Upwards from any element**: if the component says `yes` at every element
from `y` on, the iteration exits `yes` from the component's start at `y`. -/
theorem all_reach_yes {P : A → Prop} (h : ∀ y, D.Decides (vy v y) (P y)) (y : A)
    (hy : ∀ y', y ≤ y' → P y') (u : D.Coord → A) :
    ∃ c, D.all.ReachAt v (some D.start, Sum.elim u fun _ => y) c ∧ D.all.ExitAt v c true := by
  induction y using order_induction_down generalizing u with
  | hmax z hz =>
    obtain ⟨a, ha, he⟩ := ((h z u).1).mpr (hy z le_rfl)
    refine ⟨(some a.1, Sum.elim a.2 fun _ => z), reachAt_all_of_reachAt D v ha, ?_⟩
    exact (exitAt_all_some D v a.1 _ true).mpr ⟨by simpa using he, fun _ => hz⟩
  | hstep w z hwz hnb ih =>
    obtain ⟨a, ha, he⟩ := ((h w u).1).mpr (hy w le_rfl)
    obtain ⟨c, hc, hce⟩ := ih (fun y' hy' => hy y' (hwz.le.trans hy')) a.2
    refine ⟨c, ?_, hce⟩
    refine ((reachAt_all_of_reachAt D v ha).tail ?_).trans hc
    exact (stepAt_all_some_some D v a.1 D.start _ _).mpr
      (Or.inr ⟨rfl, by simpa using he, ⟨hwz, hnb⟩, rfl⟩)

/-- **Upwards to a failure**: if the component says `yes` below `y` but not
everywhere, the iteration exits `no` from the component's start at `y`. -/
theorem all_reach_no {P : A → Prop} (h : ∀ y, D.Decides (vy v y) (P y)) (hnot : ¬∀ y, P y)
    (y : A) (hy : ∀ y', y' < y → P y') (u : D.Coord → A) :
    ∃ c, D.all.ReachAt v (some D.start, Sum.elim u fun _ => y) c ∧ D.all.ExitAt v c false := by
  induction y using order_induction_down generalizing u with
  | hmax z hz =>
    have hnz : ¬P z := fun hp => hnot fun y' =>
      (lt_or_eq_of_le (hz y')).elim (hy y') fun hyz => hyz ▸ hp
    obtain ⟨a, ha, he⟩ := ((h z u).2).mpr hnz
    exact ⟨(some a.1, Sum.elim a.2 fun _ => z), reachAt_all_of_reachAt D v ha,
      (exitAt_all_some D v a.1 _ false).mpr ⟨by simpa using he, fun h => Bool.noConfusion h⟩⟩
  | hstep w z hwz hnb ih =>
    by_cases hw : P w
    · obtain ⟨a, ha, he⟩ := ((h w u).1).mpr hw
      have hlt : ∀ y', y' < z → P y' := fun y' hy' => by
        rcases lt_trichotomy y' w with hlt | rfl | hgt
        · exact hy y' hlt
        · exact hw
        · exact absurd ⟨hgt, hy'⟩ (hnb y')
      obtain ⟨c, hc, hce⟩ := ih hlt a.2
      refine ⟨c, ((reachAt_all_of_reachAt D v ha).tail ?_).trans hc, hce⟩
      exact (stepAt_all_some_some D v a.1 D.start _ _).mpr
        (Or.inr ⟨rfl, by simpa using he, ⟨hwz, hnb⟩, rfl⟩)
    · obtain ⟨a, ha, he⟩ := ((h w u).2).mpr hw
      exact ⟨(some a.1, Sum.elim a.2 fun _ => w), reachAt_all_of_reachAt D v ha,
        (exitAt_all_some D v a.1 _ false).mpr ⟨by simpa using he, fun h => Bool.noConfusion h⟩⟩

/-- What the iteration may have reached: its start, or a node of the component
at some element, every smaller element having been answered `yes`. -/
def AllInv (P : A → Prop) (t : D.Coord ⊕ Unit → A) (c : D.all.Node A) : Prop :=
  c = (none, t) ∨
    ∃ (m : D.Mode) (t' : D.Coord ⊕ Unit → A), c = (some m, t') ∧
      (∀ y', y' < t' (Sum.inr ()) → P y') ∧
        ∃ u₀, D.ReachAt (vy v (t' (Sum.inr ()))) (D.start, u₀) (m, t' ∘ Sum.inl)

omit [Finite A] in
theorem allInv_of_reachAt {P : A → Prop} (h : ∀ y, D.Decides (vy v y) (P y))
    (t : D.Coord ⊕ Unit → A) {c : D.all.Node A} (hc : D.all.ReachAt v (none, t) c) :
    AllInv D v P t c := by
  refine reach_invariant (P := AllInv D v P t) (fun a b ha hab => ?_) hc (Or.inl rfl)
  obtain ⟨mb, tb⟩ := b
  rcases ha with rfl | ⟨m, t', rfl, hlt, u₀, hr⟩
  · rcases mb with _ | mb
    · exact absurd hab (not_stepAt_all_none_none D v t tb)
    · obtain ⟨rfl, -, hmin⟩ := (stepAt_all_none_some D v mb t tb).mp hab
      exact Or.inr ⟨D.start, tb, rfl, fun y' hy' => absurd (hmin y') (not_le.mpr hy'), _,
        Relation.ReflTransGen.refl⟩
  · rcases mb with _ | mb
    · exact absurd hab (not_stepAt_all_some_none D v m t' tb)
    · rcases (stepAt_all_some_some D v m mb t' tb).mp hab with ⟨hs, hy⟩ | ⟨rfl, he, hsucc, hcp⟩
      · refine Or.inr ⟨mb, tb, rfl, ?_, u₀, ?_⟩
        · rw [hy]
          exact hlt
        · rw [hy]
          exact hr.tail hs
      · refine Or.inr ⟨D.start, tb, rfl, fun y' hy' => ?_, _, Relation.ReflTransGen.refl⟩
        rcases lt_trichotomy y' (t' (Sum.inr ())) with h1 | rfl | h1
        · exact hlt y' h1
        · exact ((h _ u₀).1).mp ⟨_, hr, he⟩
        · exact absurd ⟨h1, hy'⟩ (hsucc.2 y')

variable [Nonempty A]

theorem out_all {P : A → Prop} (h : ∀ y, D.Decides (vy v y) (P y)) (t : D.Coord ⊕ Unit → A) :
    (D.all.Out v t true ↔ ∀ y, P y) ∧ (D.all.Out v t false ↔ ¬∀ y, P y) := by
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : A, ∀ a, y₀ ≤ a := by
    obtain ⟨y₀, -, hy₀⟩ := (Finite.to_wellFoundedLT (α := A)).wf.has_min Set.univ
      ⟨Classical.arbitrary A, Set.mem_univ _⟩
    exact ⟨y₀, fun a => not_lt.mp (hy₀ a (Set.mem_univ a))⟩
  have hinit : D.all.StepAt v (none, t) (some D.start, Sum.elim (t ∘ Sum.inl) fun _ => y₀) :=
    (stepAt_all_none_some D v D.start t _).mpr ⟨rfl, by simp, hy₀⟩
  constructor
  · constructor
    · rintro ⟨c, hc, he⟩
      rcases allInv_of_reachAt D v h t hc with rfl | ⟨m, t', rfl, hlt, u₀, hr⟩
      · exact absurd he (not_exitAt_all_none D v t true)
      · obtain ⟨he, hmax⟩ := (exitAt_all_some D v m t' true).mp he
        intro y
        rcases lt_or_eq_of_le (hmax rfl y) with h1 | rfl
        · exact hlt y h1
        · exact ((h _ u₀).1).mp ⟨_, hr, he⟩
    · intro hP
      obtain ⟨c, hc, he⟩ := all_reach_yes D v h y₀ (fun y' _ => hP y') (t ∘ Sum.inl)
      exact ⟨c, Relation.ReflTransGen.head hinit hc, he⟩
  · constructor
    · rintro ⟨c, hc, he⟩
      rcases allInv_of_reachAt D v h t hc with rfl | ⟨m, t', rfl, -, u₀, hr⟩
      · exact absurd he (not_exitAt_all_none D v t false)
      · obtain ⟨he, -⟩ := (exitAt_all_some D v m t' false).mp he
        exact fun hP => ((h _ u₀).2).mp ⟨_, hr, he⟩ (hP _)
    · intro hnot
      obtain ⟨c, hc, he⟩ := all_reach_no D v h hnot y₀
        (fun y' hy' => absurd (hy₀ y') (not_le.mpr hy')) (t ∘ Sum.inl)
      exact ⟨c, Relation.ReflTransGen.head hinit hc, he⟩

/-- **The iteration decides the universal quantification.** -/
theorem decides_all {P : A → Prop} (h : ∀ y, D.Decides (vy v y) (P y)) :
    D.all.Decides v (∀ y, P y) :=
  fun t => out_all D v h t

omit [Finite A] [Nonempty A] in
theorem functional_all (h : D.Functional A) : D.all.Functional A := by
  have hsucc : ∀ w z z' : A, (w < z ∧ ∀ a, ¬(w < a ∧ a < z)) →
      (w < z' ∧ ∀ a, ¬(w < a ∧ a < z')) → z = z' := by
    intro w z z' hz hz'
    rcases lt_trichotomy z z' with h1 | h1 | h1
    · exact absurd ⟨hz.1, h1⟩ (hz'.2 z)
    · exact h1
    · exact absurd ⟨hz'.1, h1⟩ (hz.2 z')
  refine functional_of ?_ ?_ ?_
  · rintro v ⟨m, t⟩ ⟨mb, tb⟩ ⟨mc, tc⟩ hb hc
    rcases m with _ | m <;> rcases mb with _ | mb <;> rcases mc with _ | mc
    · exact absurd hb (not_stepAt_all_none_none D v t tb)
    · exact absurd hb (not_stepAt_all_none_none D v t tb)
    · exact absurd hc (not_stepAt_all_none_none D v t tc)
    · obtain ⟨rfl, hb1, hb2⟩ := (stepAt_all_none_some D v mb t tb).mp hb
      obtain ⟨rfl, hc1, hc2⟩ := (stepAt_all_none_some D v mc t tc).mp hc
      refine Prod.ext rfl (funext fun i => ?_)
      rcases i with i | ⟨⟩
      · exact (congrFun hb1 i).trans (congrFun hc1 i).symm
      · exact le_antisymm (hb2 _) (hc2 _)
    · exact absurd hb (not_stepAt_all_some_none D v m t tb)
    · exact absurd hb (not_stepAt_all_some_none D v m t tb)
    · exact absurd hc (not_stepAt_all_some_none D v m t tc)
    · rcases (stepAt_all_some_some D v m mb t tb).mp hb with ⟨hb1, hb2⟩ | ⟨rfl, hbe, hbs, hbc⟩ <;>
        rcases (stepAt_all_some_some D v m mc t tc).mp hc with ⟨hc1, hc2⟩ | ⟨rfl, hce, hcs, hcc⟩
      · have := h.step_unique hb1 hc1
        refine Prod.ext (congrArg some (congrArg Prod.fst this)) (funext fun i => ?_)
        rcases i with i | ⟨⟩
        · exact congrFun (congrArg Prod.snd this) i
        · exact hb2.trans hc2.symm
      · exact absurd hce (h.not_exit_of_step hb1)
      · exact absurd hbe (h.not_exit_of_step hc1)
      · refine Prod.ext rfl (funext fun i => ?_)
        rcases i with i | ⟨⟩
        · exact (congrFun hbc i).trans (congrFun hcc i).symm
        · exact hsucc _ _ _ hbs hcs
  · rintro v ⟨m, t⟩ ⟨mb, tb⟩ o hb he
    rcases m with _ | m
    · exact not_exitAt_all_none D v t o he
    · rcases mb with _ | mb
      · exact not_stepAt_all_some_none D v m t tb hb
      · obtain ⟨he, hmax⟩ := (exitAt_all_some D v m t o).mp he
        rcases (stepAt_all_some_some D v m mb t tb).mp hb with ⟨hb1, -⟩ | ⟨-, hbe, hbs, -⟩
        · exact h.not_exit_of_step hb1 he
        · cases o
          · exact Bool.noConfusion (h.exit_unique hbe he)
          · exact absurd (hmax rfl _) (not_le.mpr hbs.1)
  · rintro v ⟨m, t⟩ h1 h2
    rcases m with _ | m
    · exact not_exitAt_all_none D v t true h1
    · exact Bool.noConfusion (h.exit_unique ((exitAt_all_some D v m t true).mp h1).1
        ((exitAt_all_some D v m t false).mp h2).1)

end All

/-! ### Quantifying over a tuple, and the derived connectives -/

section Tuple

variable {L : Language.{0, 0}}

/-- The parameters of a decider over a tuple of `K + 1` variables, read as the
parameters over `K` variables together with one more. -/
def snocVar (β : Type) (K : ℕ) : β ⊕ Fin (K + 1) → (β ⊕ Fin K) ⊕ Unit :=
  Sum.elim (fun b => Sum.inl (Sum.inl b))
    (Fin.lastCases (Sum.inr ()) fun i => Sum.inl (Sum.inr i))

/-- **Universal quantification over a tuple**: one iteration per coordinate. -/
@[reducible]
noncomputable def allTup : {β : Type} → (K : ℕ) → Decider L (β ⊕ Fin K) → Decider L β
  | _, 0, D => D.relabelPar (Sum.elim id Fin.elim0)
  | β, K + 1, D => allTup K (D.relabelPar (snocVar β K)).all

/-- **Existential quantification over a tuple**, by De Morgan. -/
@[reducible]
noncomputable def exTup {β : Type} (K : ℕ) (D : Decider L (β ⊕ Fin K)) : Decider L β :=
  (allTup K D.neg).neg

/-- **Implication**, by De Morgan: not (the first and not the second). -/
@[reducible]
noncomputable def imp {β : Type} (D₁ D₂ : Decider L β) : Decider L β :=
  (seq D₁ D₂.neg).neg

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]

theorem decides_allTup {β : Type} (K : ℕ) (D : Decider L (β ⊕ Fin K)) (v : β → A)
    {P : (Fin K → A) → Prop} (h : ∀ xs, D.Decides (Sum.elim v xs) (P xs)) :
    (allTup K D).Decides v (∀ xs, P xs) := by
  induction K generalizing β with
  | zero =>
    refine (decides_relabelPar D _ v (P := P Fin.elim0) ?_).congr
      ⟨fun hp xs => by rw [Subsingleton.elim xs Fin.elim0]; exact hp, fun hp => hp Fin.elim0⟩
    refine (h Fin.elim0).congr_val (funext fun i => ?_)
    rcases i with i | i
    · rfl
    · exact i.elim0
  | succ K ih =>
    refine (ih (D.relabelPar (snocVar β K)).all v (P := fun xs => ∀ a, P (Fin.snoc xs a))
      fun xs => decides_all _ _ fun a => decides_relabelPar D _ _ ?_).congr ?_
    · refine (h (Fin.snoc xs a)).congr_val (funext fun i => ?_)
      rcases i with i | i
      · rfl
      · induction i using Fin.lastCases with
        | last => simp [snocVar, vy]
        | cast j => simp [snocVar, vy]
    · exact ⟨fun hp xs => Fin.snoc_init_self xs ▸ hp (Fin.init xs) (xs (Fin.last K)),
        fun hp xs a => hp _⟩

omit [Finite A] [Nonempty A] in
theorem functional_allTup {β : Type} (K : ℕ) (D : Decider L (β ⊕ Fin K)) (h : D.Functional A) :
    (allTup K D).Functional A := by
  induction K generalizing β with
  | zero => exact functional_relabelPar D _ h
  | succ K ih => exact ih _ (functional_all _ (functional_relabelPar D _ h))

theorem decides_exTup {β : Type} (K : ℕ) (D : Decider L (β ⊕ Fin K)) (v : β → A)
    {P : (Fin K → A) → Prop} (h : ∀ xs, D.Decides (Sum.elim v xs) (P xs)) :
    (exTup K D).Decides v (∃ xs, P xs) := by
  refine (decides_neg _ v (decides_allTup K D.neg v fun xs => decides_neg D _ (h xs))).congr ?_
  exact not_forall_not

omit [Finite A] [Nonempty A] in
theorem functional_exTup {β : Type} (K : ℕ) (D : Decider L (β ⊕ Fin K)) (h : D.Functional A) :
    (exTup K D).Functional A :=
  functional_neg _ (functional_allTup K D.neg (functional_neg D h))

omit [Finite A] [Nonempty A] in
theorem decides_imp {β : Type} (D₁ D₂ : Decider L β) (v : β → A) {P Q : Prop}
    (h₁ : D₁.Decides v P) (h₂ : D₂.Decides v Q) : (imp D₁ D₂).Decides v (P → Q) := by
  refine (decides_neg _ v (decides_seq D₁ D₂.neg v h₁ (decides_neg D₂ v h₂))).congr ?_
  exact not_and_not_right

omit [Finite A] [Nonempty A] in
theorem functional_imp {β : Type} (D₁ D₂ : Decider L β) (h₁ : D₁.Functional A)
    (h₂ : D₂.Functional A) : (imp D₁ D₂).Functional A :=
  functional_neg _ (functional_seq D₁ D₂.neg h₁ (functional_neg D₂ h₂))

end Tuple

/-! ### A decider with no parameters is a specification -/

section ToSpec

variable {L : Language.{0, 0}} (D : Decider L Empty)

/-- The coordinates of a decider, enumerated. -/
noncomputable def coordEquiv : D.Coord ≃ Fin (Nat.card D.Coord) :=
  letI := Fintype.ofFinite D.Coord
  (Fintype.equivFin D.Coord).trans (finCongr Fintype.card_eq_nat_card)

/-- The variables of the decider's step, as the specification's. -/
noncomputable def specVar : (D.Coord ⊕ D.Coord) ⊕ Empty →
    Fin (Nat.card D.Coord) ⊕ Fin (Nat.card D.Coord) :=
  Sum.elim (Sum.map D.coordEquiv D.coordEquiv) Empty.elim

/-- The variables of the decider's exit, as the specification's step. -/
noncomputable def specExitVar : D.Coord ⊕ Empty →
    Fin (Nat.card D.Coord) ⊕ Fin (Nat.card D.Coord) :=
  Sum.elim (fun c => Sum.inl (D.coordEquiv c)) Empty.elim

open Classical in
/-- **A decider as a specification**: the two exits become two terminal
modes, the `yes` one accepting; the start mode is the source, at any tuple. -/
@[reducible]
noncomputable def toSpec : TCSpec L where
  Mode := D.Mode ⊕ Bool
  k := Nat.card D.Coord
  step m n :=
    match m, n with
    | Sum.inl m, Sum.inl n => (D.step m n).relabel D.specVar
    | Sum.inl m, Sum.inr o =>
        (D.exit m o).relabel D.specExitVar ⊓
          copyF (fun i : Fin (Nat.card D.Coord) => Sum.inl i) Sum.inr
    | Sum.inr _, _ => ⊥
  src m :=
    match m with
    | Sum.inl m => if m = D.start then ⊤ else ⊥
    | Sum.inr _ => ⊥
  tgt m :=
    match m with
    | Sum.inr true => ⊤
    | _ => ⊥

variable {A : Type} [L.Structure A] [LinearOrder A]

/-- The valuation of the (absent) parameters. -/
abbrev noPar (A : Type) : Empty → A := fun z => z.elim

theorem step_toSpec_inl_inl (m n : D.Mode) (x x' : Fin (Nat.card D.Coord) → A) :
    D.toSpec.Step (Sum.inl m, x) (Sum.inl n, x') ↔
      D.StepAt (noPar A) (m, x ∘ D.coordEquiv) (n, x' ∘ D.coordEquiv) := by
  change Formula.Realize (M := A) ((D.step m n).relabel D.specVar) (Sum.elim x x') ↔ _
  rw [Formula.realize_relabel]
  refine iff_of_eq (congrArg (Formula.Realize (M := A) (D.step m n)) (funext fun i => ?_))
  rcases i with (i | i) | i
  · rfl
  · rfl
  · exact i.elim

theorem step_toSpec_inl_inr (m : D.Mode) (o : Bool) (x x' : Fin (Nat.card D.Coord) → A) :
    D.toSpec.Step (Sum.inl m, x) (Sum.inr o, x') ↔
      D.ExitAt (noPar A) (m, x ∘ D.coordEquiv) o ∧ x' = x := by
  change Formula.Realize (M := A) ((D.exit m o).relabel D.specExitVar ⊓
    copyF (fun i : Fin (Nat.card D.Coord) => Sum.inl i) Sum.inr) (Sum.elim x x') ↔ _
  rw [Formula.realize_inf, Formula.realize_relabel, realize_copyF]
  refine and_congr (iff_of_eq (congrArg (Formula.Realize (M := A) (D.exit m o))
    (funext fun i => ?_)))
    ⟨fun h => funext fun i => congrFun h i, fun h => funext fun i => congrFun h i⟩
  rcases i with i | i
  · rfl
  · exact i.elim

theorem not_step_toSpec_inr (o : Bool) (n : D.Mode ⊕ Bool) (x x' : Fin (Nat.card D.Coord) → A) :
    ¬D.toSpec.Step (Sum.inr o, x) (n, x') :=
  fun h => h

theorem isSrc_toSpec_inl (m : D.Mode) (x : Fin (Nat.card D.Coord) → A) :
    D.toSpec.IsSrc (Sum.inl m, x) ↔ m = D.start := by
  classical
  change (if m = D.start then (⊤ : (L.sum Language.order).Formula _) else ⊥).Realize x ↔ _
  split_ifs with h <;> simp [h]

theorem not_isSrc_toSpec_inr (o : Bool) (x : Fin (Nat.card D.Coord) → A) :
    ¬D.toSpec.IsSrc (Sum.inr o, x) :=
  fun h => h

theorem isTgt_toSpec (m : D.Mode ⊕ Bool) (x : Fin (Nat.card D.Coord) → A) :
    D.toSpec.IsTgt (m, x) ↔ m = Sum.inr true := by
  rcases m with m | (_ | _)
  · exact ⟨fun h => h.elim, fun h => absurd h Sum.inl_ne_inr⟩
  · exact ⟨fun h => h.elim, fun h => (Bool.false_ne_true (Sum.inr_injective h)).elim⟩
  · refine ⟨fun _ => rfl, fun _ => ?_⟩
    change (⊤ : (L.sum Language.order).Formula _).Realize x
    exact Formula.realize_top.mpr trivial

/-- What the specification reaches from its source: a node of the decider it
reaches, or an exit it reaches. -/
theorem toSpec_invariant (x : Fin (Nat.card D.Coord) → A) {c : D.toSpec.Node A}
    (h : D.toSpec.Reach (Sum.inl D.start, x) c) :
    (∃ (m : D.Mode) (x' : Fin (Nat.card D.Coord) → A), c = (Sum.inl m, x') ∧
        D.ReachAt (noPar A) (D.start, x ∘ D.coordEquiv) (m, x' ∘ D.coordEquiv)) ∨
      (∃ (o : Bool) (x' : Fin (Nat.card D.Coord) → A), c = (Sum.inr o, x') ∧
        D.Out (noPar A) (x ∘ D.coordEquiv) o) := by
  refine reach_invariant (P := fun c => (∃ (m : D.Mode) (x' : Fin (Nat.card D.Coord) → A),
      c = (Sum.inl m, x') ∧
        D.ReachAt (noPar A) (D.start, x ∘ D.coordEquiv) (m, x' ∘ D.coordEquiv)) ∨
      (∃ (o : Bool) (x' : Fin (Nat.card D.Coord) → A), c = (Sum.inr o, x') ∧
        D.Out (noPar A) (x ∘ D.coordEquiv) o)) (fun a b ha hab => ?_) h
    (Or.inl ⟨D.start, x, rfl, Relation.ReflTransGen.refl⟩)
  obtain ⟨mb, xb⟩ := b
  rcases ha with ⟨m, x', rfl, hr⟩ | ⟨o, x', rfl, -⟩
  · rcases mb with mb | ob
    · exact Or.inl ⟨mb, xb, rfl, hr.tail ((D.step_toSpec_inl_inl m mb x' xb).mp hab)⟩
    · obtain ⟨he, -⟩ := (D.step_toSpec_inl_inr m ob x' xb).mp hab
      exact Or.inr ⟨ob, xb, rfl, _, hr, he⟩
  · exact absurd hab (D.not_step_toSpec_inr o mb x' xb)

/-- A path of the decider is a path of the specification. -/
theorem reach_toSpec_of_reachAt {a b : D.Node A} (h : D.ReachAt (noPar A) a b) :
    D.toSpec.Reach (Sum.inl a.1, a.2 ∘ D.coordEquiv.symm)
      (Sum.inl b.1, b.2 ∘ D.coordEquiv.symm) := by
  refine Relation.ReflTransGen.lift
    (fun c : D.Node A => (Sum.inl c.1, c.2 ∘ D.coordEquiv.symm)) (fun c d hcd => ?_) _ _ h
  refine (D.step_toSpec_inl_inl c.1 d.1 _ _).mpr ?_
  simpa [Function.comp_def] using hcd

/-- **The specification accepts exactly when the decider says `yes`** from some
tuple. -/
theorem accepts_toSpec [Nonempty A] {P : Prop} (h : D.Decides (noPar A) P) :
    D.toSpec.Accepts A ↔ P := by
  constructor
  · rintro ⟨⟨mu, xu⟩, w, hu, hw, huw⟩
    rcases mu with mu | ou
    · obtain rfl := (D.isSrc_toSpec_inl mu xu).mp hu
      rcases D.toSpec_invariant xu huw with ⟨m, x', rfl, -⟩ | ⟨o, x', rfl, ho⟩
      · exact absurd ((D.isTgt_toSpec _ x').mp hw) Sum.inl_ne_inr
      · obtain rfl := Sum.inr_injective ((D.isTgt_toSpec _ x').mp hw)
        exact ((h _).1).mp ho
    · exact absurd hu (D.not_isSrc_toSpec_inr ou xu)
  · intro hP
    obtain ⟨t⟩ : Nonempty (D.Coord → A) := inferInstance
    obtain ⟨a, ha, he⟩ := ((h t).1).mpr hP
    refine ⟨(Sum.inl D.start, t ∘ D.coordEquiv.symm), (Sum.inr true, a.2 ∘ D.coordEquiv.symm),
      (D.isSrc_toSpec_inl _ _).mpr rfl, (D.isTgt_toSpec _ _).mpr rfl, ?_⟩
    refine (D.reach_toSpec_of_reachAt ha).tail ?_
    refine (D.step_toSpec_inl_inr a.1 true _ _).mpr ⟨?_, rfl⟩
    simpa [Function.comp_def] using he

/-- **A functional decider gives a functional specification.** -/
theorem functional_toSpec (h : D.Functional A) : D.toSpec.Functional A := by
  rintro ⟨m, x⟩ ⟨mb, xb⟩ ⟨mc, xc⟩ hb hc
  rcases m with m | o
  · rcases mb with mb | ob <;> rcases mc with mc | oc
    · have := h.step_unique ((D.step_toSpec_inl_inl m mb x xb).mp hb)
        ((D.step_toSpec_inl_inl m mc x xc).mp hc)
      refine Prod.ext (congrArg Sum.inl (congrArg Prod.fst this)) (funext fun i => ?_)
      have := congrFun (congrArg Prod.snd this) (D.coordEquiv.symm i)
      simpa using this
    · exact absurd ((D.step_toSpec_inl_inr m oc x xc).mp hc).1
        (fun he => h.not_exit_of_step ((D.step_toSpec_inl_inl m mb x xb).mp hb) he)
    · exact absurd ((D.step_toSpec_inl_inr m ob x xb).mp hb).1
        (fun he => h.not_exit_of_step ((D.step_toSpec_inl_inl m mc x xc).mp hc) he)
    · obtain ⟨hbe, hxb⟩ := (D.step_toSpec_inl_inr m ob x xb).mp hb
      obtain ⟨hce, hxc⟩ := (D.step_toSpec_inl_inr m oc x xc).mp hc
      rw [hxb, hxc, h.exit_unique hbe hce]
  · exact absurd hb (D.not_step_toSpec_inr o mb x xb)

/-- **A functional decider's specification is unchanged by determinization**:
its deterministic reading accepts exactly when the decider says `yes`. -/
theorem det_accepts_toSpec [Nonempty A] {P : Prop} (h : D.Decides (noPar A) P)
    (hf : D.Functional A) : D.toSpec.det.Accepts A ↔ P :=
  (D.toSpec.det_accepts_iff (D.functional_toSpec hf)).trans (D.accepts_toSpec h)

end ToSpec

end Decider

end DescriptiveComplexity
