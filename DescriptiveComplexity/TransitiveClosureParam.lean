/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.FixedPointInflationary
import DescriptiveComplexity.TransitiveClosure

/-!
# Transitive closures with parameters, as relations a formula may read

`DescriptiveComplexity.TCSpec` defines a *sentence*: a walk on tuples, and the
question whether an accepting node is reachable from a starting one. A
reduction needs more than that – its defining formulas have free variables, so
what they may consult is a **relation**, not an answer. This file provides it:
a `DescriptiveComplexity.ParamTCSpec` is a walk whose step formula may mention
`par` parameters besides its two tuples, and the relation it defines is
reachability itself,

`R[m,m'](x̄, ȳ, z̄)` – “from the node `(m, x̄)` the node `(m', ȳ)` is reachable,
the parameters being `z̄`” –

one relation per ordered pair of modes. A finite family of such walks
(`DescriptiveComplexity.TCFamily`) is a block of relation variables
(`DescriptiveComplexity.TCFamily.block`) whose assignment is fixed, not
guessed: `DescriptiveComplexity.TCFamily.reachAssign`. A structure expanded by
it is what the formulas of an FO(TC) reduction are read over
(`DescriptiveComplexity.TransitiveClosureReduction`).

## Reachability is an inflationary induction

The theorem of this file is
`DescriptiveComplexity.TCFamily.inflLimit_toStepDef`: the reachability
relations of a family are the value of one simultaneous inflationary induction
(`DescriptiveComplexity.TCFamily.toStepDef`), namely the rules

* `R[m,m](x̄, x̄, z̄)`, and
* `R[m,m'](x̄, ȳ, z̄) ← R[m,m''](x̄, ȳ', z̄) ∧ step[m'',m'](ȳ', ȳ, z̄)`.

They are *positive* in the relation variables, so the inflationary iteration
computes the least fixed point, which is `Relation.ReflTransGen` of the step –
the mode pairs being static, each rule is one step formula, and no clausal
apparatus is needed.

That theorem is what makes an FO(TC) reduction an FO(LFP) reduction, and so
what gives the FO(TC) reductions their closure properties without a second
development. It is also the honest statement of where FO(TC) sits: a walk is a
fixed point of a very restricted shape.

## Reading an FO(TC) *sentence* off the relations

`DescriptiveComplexity.TCSpec.acceptsF` turns any existing
`DescriptiveComplexity.TCSpec` into a formula over the expansion by its own
reachability relations: “some accepting node is reachable from some starting
node”, with the walk itself now an atom rather than an operator
(`DescriptiveComplexity.TCSpec.realize_acceptsF`). Every FO(TC) definable
property is thereby available to an FO(TC) reduction as a formula, which is how
`DescriptiveComplexity.EVEN` enters `DescriptiveComplexity.TCReduction`.
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Walks with parameters -/

/-- A **parameterized transitive-closure specification**: a walk on `k`-tuples
carrying a finite mode, whose step formula may mention `par` parameters beside
the current and the next tuple. Unlike `DescriptiveComplexity.TCSpec` it has no
`src`/`tgt` formulas: what it defines is the reachability *relation*, and where
a sentence is wanted the endpoints are supplied by the formula that reads it.

The vocabulary is a parameter, not the ordered expansion: the ordered reading
is the instance `L := L₀.sum Language.order`, as for
`DescriptiveComplexity.StepDef`. -/
structure ParamTCSpec (L : Language.{0, 0}) : Type 1 where
  /-- The modes: the finite control the walk carries beside its tuple. -/
  Mode : Type
  /-- Modes are finite. -/
  [modeFinite : Finite Mode]
  /-- The walk runs on `k`-tuples of elements. -/
  k : ℕ
  /-- The number of parameters the step formula may mention. -/
  par : ℕ
  /-- The step formula, one per pair of modes: the current tuple, the next
  tuple, then the parameters. -/
  step : Mode → Mode → L.Formula ((Fin k ⊕ Fin k) ⊕ Fin par)

attribute [instance] ParamTCSpec.modeFinite

namespace ParamTCSpec

variable {L : Language.{0, 0}} (s : ParamTCSpec L) {A : Type} [L.Structure A]

variable (A) in
/-- A node of the walk: a mode together with a `k`-tuple. -/
abbrev Node : Type := s.Mode × (Fin s.k → A)

/-- One step of the walk, at a valuation of the parameters. -/
def StepAt (z : Fin s.par → A) (a b : s.Node A) : Prop :=
  (s.step a.1 b.1).Realize (Sum.elim (Sum.elim a.2 b.2) z)

/-- Reachability in the walk, at a valuation of the parameters. -/
abbrev ReachAt (z : Fin s.par → A) : s.Node A → s.Node A → Prop :=
  Relation.ReflTransGen (s.StepAt z)

/-! #### Packing a tuple, two endpoints and the parameters -/

/-- The position of the `i`-th coordinate of the *first* tuple. -/
def leftIx (i : Fin s.k) : Fin (s.k + s.k + s.par) := ⟨i, by have := i.isLt; omega⟩

/-- The position of the `i`-th coordinate of the *second* tuple. -/
def rightIx (i : Fin s.k) : Fin (s.k + s.k + s.par) := ⟨s.k + i, by have := i.isLt; omega⟩

/-- The position of the `j`-th parameter. -/
def parIx (j : Fin s.par) : Fin (s.k + s.k + s.par) := ⟨s.k + s.k + j, by have := j.isLt; omega⟩

variable {s}

/-- The tuple assembled from two endpoints and a valuation of the
parameters. -/
def pack {V : Type} (x y : Fin s.k → V) (z : Fin s.par → V) : Fin (s.k + s.k + s.par) → V :=
  fun j =>
    if h : (j : ℕ) < s.k then x ⟨j, h⟩
    else if h2 : (j : ℕ) < s.k + s.k then y ⟨(j : ℕ) - s.k, by omega⟩
    else z ⟨(j : ℕ) - (s.k + s.k), by have := j.isLt; omega⟩

@[simp]
theorem pack_left {V : Type} (x y : Fin s.k → V) (z : Fin s.par → V) (i : Fin s.k) :
    pack x y z (s.leftIx i) = x i := by
  have hi : ((s.leftIx i : Fin (s.k + s.k + s.par)) : ℕ) < s.k := i.isLt
  simp only [pack]
  rw [dif_pos hi]
  exact congrArg x (Fin.ext rfl)

@[simp]
theorem pack_right {V : Type} (x y : Fin s.k → V) (z : Fin s.par → V) (i : Fin s.k) :
    pack x y z (s.rightIx i) = y i := by
  have hi := i.isLt
  have h1 : ¬(((s.rightIx i : Fin (s.k + s.k + s.par)) : ℕ) < s.k) := by
    simp only [rightIx]; omega
  have h2 : ((s.rightIx i : Fin (s.k + s.k + s.par)) : ℕ) < s.k + s.k := by
    simp only [rightIx]; omega
  simp only [pack]
  rw [dif_neg h1, dif_pos h2]
  exact congrArg y (Fin.ext (by simp only [rightIx]; omega))

@[simp]
theorem pack_par {V : Type} (x y : Fin s.k → V) (z : Fin s.par → V) (j : Fin s.par) :
    pack x y z (s.parIx j) = z j := by
  have hj := j.isLt
  have h1 : ¬(((s.parIx j : Fin (s.k + s.k + s.par)) : ℕ) < s.k) := by
    simp only [parIx]; omega
  have h2 : ¬(((s.parIx j : Fin (s.k + s.k + s.par)) : ℕ) < s.k + s.k) := by
    simp only [parIx]; omega
  simp only [pack]
  rw [dif_neg h1, dif_neg h2]
  exact congrArg z (Fin.ext (by simp only [parIx]; omega))

/-- Every tuple is packed from its three parts. -/
theorem pack_eta {V : Type} (w : Fin (s.k + s.k + s.par) → V) :
    pack (fun i => w (s.leftIx i)) (fun i => w (s.rightIx i)) (fun j => w (s.parIx j)) = w := by
  funext j
  have hj := j.isLt
  rcases Nat.lt_or_ge (j : ℕ) s.k with h | h
  · have hje : j = s.leftIx ⟨j, h⟩ := Fin.ext rfl
    rw [hje, pack_left]
  · rcases Nat.lt_or_ge (j : ℕ) (s.k + s.k) with h2 | h2
    · have hje : j = s.rightIx ⟨(j : ℕ) - s.k, by omega⟩ :=
        Fin.ext (by simp only [rightIx]; omega)
      rw [hje, pack_right]
    · have hje : j = s.parIx ⟨(j : ℕ) - (s.k + s.k), by omega⟩ :=
        Fin.ext (by simp only [parIx]; omega)
      rw [hje, pack_par]

/-- Post-composing a packed tuple with a function packs the components. -/
theorem pack_comp {V W : Type} (f : V → W) (x y : Fin s.k → V) (z : Fin s.par → V) :
    (fun j => f (pack x y z j)) =
      pack (fun t => f (x t)) (fun t => f (y t)) (fun t => f (z t)) := by
  funext j
  have hj := j.isLt
  rcases Nat.lt_or_ge (j : ℕ) s.k with h | h
  · have hje : j = s.leftIx ⟨j, h⟩ := Fin.ext rfl
    rw [hje, pack_left, pack_left]
  · rcases Nat.lt_or_ge (j : ℕ) (s.k + s.k) with h2 | h2
    · have hje : j = s.rightIx ⟨(j : ℕ) - s.k, by omega⟩ :=
        Fin.ext (by simp only [rightIx]; omega)
      rw [hje, pack_right, pack_right]
    · have hje : j = s.parIx ⟨(j : ℕ) - (s.k + s.k), by omega⟩ :=
        Fin.ext (by simp only [parIx]; omega)
      rw [hje, pack_par, pack_par]

end ParamTCSpec

/-! ### A family of walks, as a block of relation variables -/

/-- A finite family of parameterized walks. Its relation variables – one per
walk and ordered pair of that walk's modes – are what an FO(TC) reduction's
formulas may read. -/
structure TCFamily (L : Language.{0, 0}) : Type 1 where
  /-- The index type of the family. -/
  Ix : Type
  /-- The family is finite. -/
  [ixFinite : Finite Ix]
  /-- The walk of each index. -/
  spec : Ix → ParamTCSpec L

attribute [instance] TCFamily.ixFinite

namespace TCFamily

variable {L : Language.{0, 0}} (F : TCFamily L)

/-- The block of relation variables of a family: one variable per walk and
ordered pair of modes, of arity “two tuples and the parameters”. -/
def block : SOBlock where
  ι := Σ i : F.Ix, (F.spec i).Mode × (F.spec i).Mode
  arity := fun q => (F.spec q.1).k + (F.spec q.1).k + (F.spec q.1).par

variable {F} {A : Type} [L.Structure A]

/-- The assignment the block *has*, as opposed to one a second-order
quantifier would guess: each variable holds the reachability relation of its
walk, at the parameters read off the tuple. -/
def reachAssign (F : TCFamily L) (A : Type) [L.Structure A] : F.block.Assignment A :=
  fun q w =>
    (F.spec q.1).ReachAt (fun j => w ((F.spec q.1).parIx j))
      (q.2.1, fun i => w ((F.spec q.1).leftIx i))
      (q.2.2, fun i => w ((F.spec q.1).rightIx i))

/-- The reachability assignment, unfolded at a tuple. -/
theorem reachAssign_iff (q : F.block.ι) (w : Fin (F.block.arity q) → A) :
    F.reachAssign A q w ↔ (F.spec q.1).ReachAt (fun t => w ((F.spec q.1).parIx t))
      (q.2.1, fun t => w ((F.spec q.1).leftIx t))
      (q.2.2, fun t => w ((F.spec q.1).rightIx t)) :=
  Iff.rfl

theorem reachAssign_pack (q : F.block.ι) (x y : Fin (F.spec q.1).k → A)
    (z : Fin (F.spec q.1).par → A) :
    F.reachAssign A q (ParamTCSpec.pack x y z) ↔
      (F.spec q.1).ReachAt z (q.2.1, x) (q.2.2, y) := by
  simp only [reachAssign, ParamTCSpec.pack_left, ParamTCSpec.pack_right,
    ParamTCSpec.pack_par]

/-! ### The induction that computes reachability -/

section StepFormulas

variable (F)

open Classical in
/-- The reflexivity rule, as a formula: the two tuples agree – and the two
modes, which is decided statically. -/
noncomputable def diagF (q : F.block.ι) : (L.sum F.block.lang).Formula (Fin (F.block.arity q)) :=
  if q.2.1 = q.2.2 then
    Formula.iInf fun t : Fin (F.spec q.1).k =>
      Term.equal (Term.var ((F.spec q.1).leftIx t)) (Term.var ((F.spec q.1).rightIx t))
  else ⊥

/-- The atom “the first tuple reaches the freshly quantified one, in mode
`m`”. -/
noncomputable def reachAtomF (q : F.block.ι) (m : (F.spec q.1).Mode) :
    (L.sum F.block.lang).Formula (Fin (F.block.arity q) ⊕ Fin (F.spec q.1).k) :=
  Relations.formula (varInSym L F.block ⟨q.1, (q.2.1, m)⟩) fun j =>
    Term.var (ParamTCSpec.pack (V := Fin (F.block.arity q) ⊕ Fin (F.spec q.1).k)
      (fun t => Sum.inl ((F.spec q.1).leftIx t)) (fun t => Sum.inr t)
      (fun t => Sum.inl ((F.spec q.1).parIx t)) j)

/-- The last step of the walk: from the freshly quantified tuple, in mode `m`,
to the second tuple, in the variable's second mode. -/
noncomputable def lastStepF (q : F.block.ι) (m : (F.spec q.1).Mode) :
    (L.sum F.block.lang).Formula (Fin (F.block.arity q) ⊕ Fin (F.spec q.1).k) :=
  (LHom.sumInl.onFormula ((F.spec q.1).step m q.2.2)).relabel fun v =>
    match v with
    | Sum.inl (Sum.inl t) => Sum.inr t
    | Sum.inl (Sum.inr t) => Sum.inl ((F.spec q.1).rightIx t)
    | Sum.inr t => Sum.inl ((F.spec q.1).parIx t)

/-- The step formula of a relation variable: reflexivity, or one more step
after a shorter walk. Both disjuncts are positive in the relation variables,
so the inflationary iteration computes the least fixed point. -/
noncomputable def stepF (q : F.block.ι) :
    (L.sum F.block.lang).Formula (Fin (F.block.arity q)) :=
  F.diagF q ⊔
    Formula.iExs (Fin (F.spec q.1).k)
      (Formula.iSup fun m : (F.spec q.1).Mode => F.reachAtomF q m ⊓ F.lastStepF q m)

/-- **The induction of a family**: one simultaneous inflationary induction
whose relation variables are the family's, and whose value is its
reachability relations (`DescriptiveComplexity.TCFamily.inflLimit_toStepDef`).
Its output sentence is never read. -/
noncomputable def toStepDef : StepDef L where
  B := F.block
  step := F.stepF
  out := ⊤

end StepFormulas

/-! ### Realization of the step formulas -/

section Realize

variable (ρ : F.block.Assignment A)

theorem realize_diagF (q : F.block.ι) (w : Fin (F.block.arity q) → A) :
    (@Formula.Realize _ A (F.block.structure₁ (L := L) ρ) _ (F.diagF q) w) ↔
      q.2.1 = q.2.2 ∧ ∀ t, w ((F.spec q.1).leftIx t) = w ((F.spec q.1).rightIx t) := by
  classical
  let := F.block.structure₁ (L := L) ρ
  rw [diagF]
  split_ifs with h
  · simp only [Formula.realize_iInf, Formula.realize_equal]
    exact ⟨fun hw => ⟨h, hw⟩, fun hw => hw.2⟩
  · simp only [Formula.realize_bot, false_iff, not_and]
    exact fun h' => absurd h' h

theorem realize_reachAtomF (q : F.block.ι) (m : (F.spec q.1).Mode)
    (w : Fin (F.block.arity q) → A) (y : Fin (F.spec q.1).k → A) :
    (@Formula.Realize _ A (F.block.structure₁ (L := L) ρ) _ (F.reachAtomF q m) (Sum.elim w y)) ↔
      ρ ⟨q.1, (q.2.1, m)⟩ (ParamTCSpec.pack (fun t => w ((F.spec q.1).leftIx t)) y
        fun t => w ((F.spec q.1).parIx t)) := by
  let := F.block.structure₁ (L := L) ρ
  rw [reachAtomF, Formula.realize_rel]
  refine iff_of_eq (congrArg (ρ ⟨q.1, (q.2.1, m)⟩) ?_)
  exact ParamTCSpec.pack_comp (s := F.spec q.1) (Sum.elim w y) _ _ _

theorem realize_lastStepF (q : F.block.ι) (m : (F.spec q.1).Mode)
    (w : Fin (F.block.arity q) → A) (y : Fin (F.spec q.1).k → A) :
    (@Formula.Realize _ A (F.block.structure₁ (L := L) ρ) _ (F.lastStepF q m) (Sum.elim w y)) ↔
      (F.spec q.1).StepAt (fun t => w ((F.spec q.1).parIx t)) (m, y)
        (q.2.2, fun t => w ((F.spec q.1).rightIx t)) := by
  let := F.block.structure₁ (L := L) ρ
  rw [lastStepF, Formula.realize_relabel, LHom.realize_onFormula]
  refine iff_of_eq (congrArg ((F.spec q.1).step m q.2.2).Realize ?_)
  funext v
  rcases v with (t | t) | t <;> rfl

theorem realize_stepF (q : F.block.ι) (w : Fin (F.block.arity q) → A) :
    (@Formula.Realize _ A (F.block.structure₁ (L := L) ρ) _ (F.stepF q) w) ↔
      (q.2.1 = q.2.2 ∧ ∀ t, w ((F.spec q.1).leftIx t) = w ((F.spec q.1).rightIx t)) ∨
        ∃ (y : Fin (F.spec q.1).k → A) (m : (F.spec q.1).Mode),
          ρ ⟨q.1, (q.2.1, m)⟩ (ParamTCSpec.pack (fun t => w ((F.spec q.1).leftIx t)) y
              fun t => w ((F.spec q.1).parIx t)) ∧
            (F.spec q.1).StepAt (fun t => w ((F.spec q.1).parIx t)) (m, y)
              (q.2.2, fun t => w ((F.spec q.1).rightIx t)) := by
  let := F.block.structure₁ (L := L) ρ
  rw [stepF, Formula.realize_sup, F.realize_diagF ρ q w, Formula.realize_iExs]
  refine or_congr Iff.rfl (exists_congr fun y => ?_)
  rw [Formula.realize_iSup]
  refine exists_congr fun m => ?_
  rw [Formula.realize_inf, F.realize_reachAtomF ρ q m w y, F.realize_lastStepF ρ q m w y]

end Realize

/-! ### The value of the induction is the reachability relations -/

section Limit

variable [Finite A]

omit [Finite A] in
private theorem inflStage_le_reachAssign (n : ℕ) (q : F.block.ι)
    (w : Fin (F.block.arity q) → A) (h : (F.toStepDef).inflStage A n q w) :
    F.reachAssign A q w := by
  induction n generalizing q w with
  | zero => exact h.elim
  | succ n ih =>
    rw [StepDef.inflStage_succ] at h
    rcases h with h | h
    · exact ih q w h
    · rcases (F.realize_stepF ((F.toStepDef).inflStage A n) q w).mp h with
        ⟨hmode, hw⟩ | ⟨y, m, hreach, hlast⟩
      · refine (reachAssign_iff q w).mpr ?_
        have hEq : (fun t => w ((F.spec q.1).rightIx t)) = fun t => w ((F.spec q.1).leftIx t) :=
          funext fun t => (hw t).symm
        rw [hEq, ← hmode]
      · have hprev : (F.spec q.1).ReachAt (fun t => w ((F.spec q.1).parIx t))
            (q.2.1, fun t => w ((F.spec q.1).leftIx t)) (m, y) := by
          have h2 := ih ⟨q.1, (q.2.1, m)⟩ _ hreach
          simpa only [reachAssign, ParamTCSpec.pack_left, ParamTCSpec.pack_right,
            ParamTCSpec.pack_par] using h2
        exact (reachAssign_iff q w).mpr (hprev.tail hlast)

private theorem reachAt_le_inflLimit (i : F.Ix) (m : (F.spec i).Mode)
    (x : Fin (F.spec i).k → A) (z : Fin (F.spec i).par → A) (b : (F.spec i).Node A)
    (h : (F.spec i).ReachAt z (m, x) b) :
    (F.toStepDef).inflLimit A ⟨i, (m, b.1)⟩ (ParamTCSpec.pack x b.2 z) := by
  induction h with
  | refl =>
    refine ⟨1, ?_⟩
    rw [StepDef.inflStage_succ]
    exact Or.inr ((F.realize_stepF ((F.toStepDef).inflStage A 0) ⟨i, (m, m)⟩ _).mpr
      (Or.inl ⟨rfl, fun t => (ParamTCSpec.pack_left x x z t).trans
        (ParamTCSpec.pack_right x x z t).symm⟩))
  | @tail c d _ hcd ih =>
    have hfix := (F.toStepDef).isFixedPt_inflStep_inflLimit A
    have hnext : (F.toStepDef).next ((F.toStepDef).inflLimit A) ⟨i, (m, d.1)⟩
        (ParamTCSpec.pack x d.2 z) := by
      refine (F.realize_stepF ((F.toStepDef).inflLimit A) ⟨i, (m, d.1)⟩ _).mpr
        (Or.inr ⟨c.2, c.1, ?_, ?_⟩)
      · simpa only [ParamTCSpec.pack_left, ParamTCSpec.pack_par] using ih
      · simpa only [ParamTCSpec.pack_par, ParamTCSpec.pack_right] using hcd
    have hstep := congrFun (congrFun hfix ⟨i, (m, d.1)⟩) (ParamTCSpec.pack x d.2 z)
    exact (iff_of_eq hstep).mp (Or.inr hnext)

/-- **Reachability is an inflationary induction**: the value of
`DescriptiveComplexity.TCFamily.toStepDef` is the family's reachability
relations. -/
theorem inflLimit_toStepDef : (F.toStepDef).inflLimit A = F.reachAssign A := by
  funext q w
  refine propext ⟨fun ⟨n, hn⟩ => inflStage_le_reachAssign n q w hn, fun h => ?_⟩
  have h' := (reachAssign_iff q w).mp h
  have hlim := reachAt_le_inflLimit q.1 q.2.1 (fun t => w ((F.spec q.1).leftIx t))
    (fun t => w ((F.spec q.1).parIx t))
    (q.2.2, fun t => w ((F.spec q.1).rightIx t)) h'
  rwa [ParamTCSpec.pack_eta (s := F.spec q.1) w] at hlim

end Limit

end TCFamily

/-! ### An FO(TC) sentence, as a formula over the reachability relations -/

namespace TCSpec

variable {L₀ : Language.{0, 0}} (spec : TCSpec L₀)

/-- A `DescriptiveComplexity.TCSpec` read as a parameterized walk with no
parameters, over the ordered expansion its formulas already live in.

Reducible, so that the modes and the arity of the reading are those of the
specification transparently – a node of one *is* a node of the other. -/
@[reducible]
noncomputable def toParam : ParamTCSpec (L₀.sum Language.order) where
  Mode := spec.Mode
  k := spec.k
  par := 0
  step := fun m m' => (spec.step m m').relabel Sum.inl

/-- The one-element family of walks of a `DescriptiveComplexity.TCSpec`. -/
@[reducible]
noncomputable def toFamily : TCFamily (L₀.sum Language.order) where
  Ix := Unit
  spec := fun _ => spec.toParam

variable {A : Type} [L₀.Structure A] [LinearOrder A]

theorem stepAt_toParam (z : Fin 0 → A) (a b : spec.Node A) :
    spec.toParam.StepAt z a b ↔ spec.Step a b := by
  simp only [ParamTCSpec.StepAt, TCSpec.Step, toParam, Formula.realize_relabel]
  exact iff_of_eq (congrArg (spec.step a.1 b.1).Realize (funext fun v => rfl))

theorem reachAt_toParam (z : Fin 0 → A) (a b : spec.Node A) :
    spec.toParam.ReachAt z a b ↔ spec.Reach a b := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih => exact ih.tail ((spec.stepAt_toParam z c d).mp hcd)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih => exact ih.tail ((spec.stepAt_toParam z c d).mpr hcd)

/-- The reachability atom of the walk, with both endpoints quantified. -/
noncomputable def reachAtomAcc (p : spec.Mode × spec.Mode) :
    ((L₀.sum Language.order).sum spec.toFamily.block.lang).Formula
      (Empty ⊕ (Fin spec.k ⊕ Fin spec.k)) :=
  Relations.formula (varInSym (L₀.sum Language.order) spec.toFamily.block ⟨(), p⟩) fun j =>
    Term.var (ParamTCSpec.pack (V := Empty ⊕ (Fin spec.k ⊕ Fin spec.k))
      (fun t => Sum.inr (Sum.inl t)) (fun t => Sum.inr (Sum.inr t)) Fin.elim0 j)

theorem realize_reachAtomAcc (p : spec.Mode × spec.Mode)
    (v : (Empty ⊕ (Fin spec.k ⊕ Fin spec.k)) → A) :
    (@Formula.Realize _ A
      (spec.toFamily.block.structure₁ (L := L₀.sum Language.order)
        (spec.toFamily.reachAssign A)) _ (spec.reachAtomAcc p) v) ↔
      spec.Reach (p.1, fun t => v (Sum.inr (Sum.inl t)))
        (p.2, fun t => v (Sum.inr (Sum.inr t))) := by
  let := spec.toFamily.block.structure₁ (L := L₀.sum Language.order) (spec.toFamily.reachAssign A)
  rw [reachAtomAcc, Formula.realize_rel]
  refine Iff.trans (iff_of_eq (congrArg (spec.toFamily.reachAssign A ⟨(), p⟩)
    (ParamTCSpec.pack_comp (s := spec.toParam) v _ _ _))) ?_
  refine Iff.trans (TCFamily.reachAssign_pack (F := spec.toFamily) ⟨(), p⟩ _ _ _) ?_
  exact spec.reachAt_toParam _ _ _

open Classical in
/-- **The walk as an atom**: “some accepting node is reachable from some
starting node”, written over the vocabulary expanded by the walk's own
reachability relations. This is what makes every FO(TC) definable property
available to an FO(TC) reduction. -/
noncomputable def acceptsF :
    ((L₀.sum Language.order).sum spec.toFamily.block.lang).Sentence :=
  Formula.iSup fun p : spec.Mode × spec.Mode =>
    Formula.iExs (Fin spec.k ⊕ Fin spec.k)
      (((LHom.sumInl.onFormula (spec.src p.1)).relabel fun t => Sum.inr (Sum.inl t)) ⊓
        spec.reachAtomAcc p ⊓
        ((LHom.sumInl.onFormula (spec.tgt p.2)).relabel fun t => Sum.inr (Sum.inr t)))

/-- **The walk-as-an-atom formula says acceptance**, when the relation
variables hold the reachability relations they are meant to. -/
theorem realize_acceptsF :
    (@Sentence.Realize _ A
      (spec.toFamily.block.structure₁ (L := L₀.sum Language.order)
        (spec.toFamily.reachAssign A)) spec.acceptsF) ↔ spec.Accepts A := by
  classical
  let := spec.toFamily.block.structure₁ (L := L₀.sum Language.order)
    (spec.toFamily.reachAssign A)
  rw [Sentence.Realize, acceptsF, Formula.realize_iSup]
  constructor
  · rintro ⟨p, hp⟩
    rw [Formula.realize_iExs] at hp
    obtain ⟨v, hv⟩ := hp
    rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_relabel,
      Formula.realize_relabel, LHom.realize_onFormula, LHom.realize_onFormula,
      spec.realize_reachAtomAcc p] at hv
    exact ⟨(p.1, fun t => v (Sum.inl t)), (p.2, fun t => v (Sum.inr t)),
      hv.1.1, hv.2, hv.1.2⟩
  · rintro ⟨u, w, hu, hw, huw⟩
    refine ⟨(u.1, w.1), ?_⟩
    rw [Formula.realize_iExs]
    refine ⟨Sum.elim u.2 w.2, ?_⟩
    rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_relabel,
      Formula.realize_relabel, LHom.realize_onFormula, LHom.realize_onFormula,
      spec.realize_reachAtomAcc (u.1, w.1)]
    exact ⟨⟨hu, huw⟩, hw⟩

end TCSpec

end DescriptiveComplexity
