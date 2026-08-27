/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.TransitiveClosureDecideFormula
import DescriptiveComplexity.TransitiveClosureCompl

/-!
# Deciding reachability in a walk: Immerman–Szelepcsényi with parameters

The atom case of the normal form for FO(TC): the reachability relation of a
parameterized walk (`DescriptiveComplexity.ParamTCSpec`) has a
`DescriptiveComplexity.Decider` (`DescriptiveComplexity.ParamTCSpec.reachDecider`).
Its `yes` exit is the walk itself, run from the first endpoint until it
stands on the second; its `no` exit is the inductive-counting walk of
`DescriptiveComplexity.TransitiveClosureCompl`, which certifies that the second
endpoint is *not* reached.

## Parameters as constants

The complement construction is stated for a *sentence*: a
`DescriptiveComplexity.TCSpec`, whose source and target formulas have no free
variables beyond the tuple. What is needed here is the complement of a
*relation* – the parameters of the walk and its two endpoints are free. The
two are reconciled without touching the 950 lines of the counting machine:
the free variables become **constants of the vocabulary**
(`FirstOrder.Language.withConstants`), the walk becomes a sentence over the
enlarged vocabulary (`DescriptiveComplexity.ParamTCSpec.constSpec`), the
complement is taken there, and its formulas are read back with the constants
as variables (`DescriptiveComplexity.fromConst`). Mathlib's
`FirstOrder.Language.BoundedFormula.constantsVarsEquiv` is the bridge, in both
directions, and a structure interprets the constants by the valuation of the
parameters (`DescriptiveComplexity.constStructure`).
-/

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Formulas with parameters, as sentences with constants -/

section Constants

variable {L₀ : Language.{0, 0}} {γ : Type}

/-- The vocabulary with one constant per parameter. -/
abbrev withPar (L₀ : Language.{0, 0}) (γ : Type) : Language.{0, 0} := L₀[[γ]]

variable (L₀ γ) in
/-- The vocabulary map reading the second copy of the order, in the ordered
expansion of the vocabulary with constants, as the first. -/
noncomputable def collapseOrder : (withPar (L₀.sum Language.order) γ).sum Language.order →ᴸ
    withPar (L₀.sum Language.order) γ :=
  LHom.sumElim (LHom.id _) (LHom.sumInl.comp LHom.sumInr)

/-- A formula with parameters, as a formula over the vocabulary with
constants, over its ordered expansion. -/
noncomputable def toConst {β : Type} (φ : (L₀.sum Language.order).Formula (γ ⊕ β)) :
    ((withPar (L₀.sum Language.order) γ).sum Language.order).Formula β :=
  LHom.sumInl.onFormula (BoundedFormula.constantsVarsEquiv.symm φ)

/-- A formula over the ordered expansion of the vocabulary with constants, as
a formula with parameters. -/
noncomputable def fromConst {β : Type}
    (φ : ((withPar (L₀.sum Language.order) γ).sum Language.order).Formula β) :
    (L₀.sum Language.order).Formula (γ ⊕ β) :=
  BoundedFormula.constantsVarsEquiv ((collapseOrder L₀ γ).onFormula φ)

variable {A : Type} [L₀.Structure A] [LinearOrder A]

/-- The structure over the vocabulary with constants, the constants read by a
valuation of the parameters. -/
@[instance_reducible]
noncomputable def constStructure (c : γ → A) : (withPar (L₀.sum Language.order) γ).Structure A :=
  letI := constantsOn.structure c
  inferInstance

theorem realize_toConst {β : Type} (c : γ → A) (φ : (L₀.sum Language.order).Formula (γ ⊕ β))
    (u : β → A) :
    (@Formula.Realize _ A (letI := constStructure (L₀ := L₀) c; inferInstance) _ (toConst φ) u) ↔
      φ.Realize (Sum.elim c u) := by
  let := constStructure (L₀ := L₀) c
  rw [toConst, LHom.realize_onFormula]
  have hcon : (fun a : γ => (((L₀.sum Language.order).con a :
      (withPar (L₀.sum Language.order) γ).Constants) : A)) = c := funext fun a => rfl
  have := BoundedFormula.realize_constantsVarsEquiv (M := A)
    (φ := BoundedFormula.constantsVarsEquiv.symm φ) (v := u) (xs := default)
  rw [Equiv.apply_symm_apply, hcon] at this
  exact this.symm

theorem realize_fromConst {β : Type} (c : γ → A)
    (φ : ((withPar (L₀.sum Language.order) γ).sum Language.order).Formula β) (u : β → A) :
    (fromConst φ).Realize (Sum.elim c u) ↔
      (@Formula.Realize _ A (letI := constStructure (L₀ := L₀) c; inferInstance) _ φ u) := by
  let := constStructure (L₀ := L₀) c
  let : (collapseOrder L₀ γ).IsExpansionOn A :=
    ⟨fun {n} f x => by
        rcases f with f | f
        · rfl
        · exact isEmptyElim f,
      fun {n} R x => by
        rcases R with R | R
        · rfl
        · cases R
          rfl⟩
  rw [fromConst]
  have := BoundedFormula.realize_constantsVarsEquiv (M := A)
    (φ := (collapseOrder L₀ γ).onFormula φ) (v := u) (xs := default)
  refine this.trans ?_
  exact LHom.realize_onFormula _ _

end Constants

/-! ### A parameterized walk, as a sentence over the vocabulary with constants -/

namespace ParamTCSpec

variable {L : Language.{0, 0}} (W : ParamTCSpec (L.sum Language.order))

/-- The parameters of the reachability atom of a walk: the two endpoints and
the walk's own parameters, packed as `DescriptiveComplexity.ParamTCSpec.pack`
does. -/
abbrev AtomPar : Type := Fin (W.k + W.k + W.par)

/-- The variables of the step formula, the walk's parameters read off the
atom's parameters. -/
def constStepVar : (Fin W.k ⊕ Fin W.k) ⊕ Fin W.par → W.AtomPar ⊕ (Fin W.k ⊕ Fin W.k)
  | Sum.inl p => Sum.inr p
  | Sum.inr j => Sum.inl (W.parIx j)

/-- “The tuple is the first endpoint.” -/
noncomputable def eqLeftF : (L.sum Language.order).Formula (W.AtomPar ⊕ Fin W.k) :=
  Formula.iInf fun i => Term.equal (Term.var (Sum.inr i)) (Term.var (Sum.inl (W.leftIx i)))

/-- “The tuple is the second endpoint.” -/
noncomputable def eqRightF : (L.sum Language.order).Formula (W.AtomPar ⊕ Fin W.k) :=
  Formula.iInf fun i => Term.equal (Term.var (Sum.inr i)) (Term.var (Sum.inl (W.rightIx i)))

open Classical in
/-- **The walk as a sentence** over the vocabulary with one constant per
parameter of the atom: the same walk, whose sources are the first endpoint
in the first mode and whose targets are the second endpoint in the second
mode. Reducible: a node of it *is* a node of the walk. -/
@[reducible]
noncomputable def constSpec (ma mb : W.Mode) :
    TCSpec (withPar (L.sum Language.order) W.AtomPar) where
  Mode := W.Mode
  k := W.k
  step m n := toConst ((W.step m n).relabel W.constStepVar)
  src m := if m = ma then toConst W.eqLeftF else ⊥
  tgt m := if m = mb then toConst W.eqRightF else ⊥

variable {A : Type} [L.Structure A] [LinearOrder A] (ma mb : W.Mode) (w : W.AtomPar → A)

theorem constSpec_step (a b : W.Node A) :
    (letI := constStructure (L₀ := L) w; (W.constSpec ma mb).Step a b) ↔
      W.StepAt (w ∘ W.parIx) a b := by
  change (@Formula.Realize _ A (letI := constStructure (L₀ := L) w; inferInstance) _
    (toConst ((W.step a.1 b.1).relabel W.constStepVar)) (Sum.elim a.2 b.2)) ↔ _
  rw [realize_toConst, Formula.realize_relabel]
  refine iff_of_eq (congrArg (Formula.Realize (M := A) (W.step a.1 b.1)) (funext fun i => ?_))
  rcases i with (i | i) | i <;> rfl

theorem constSpec_isSrc (a : W.Node A) :
    (letI := constStructure (L₀ := L) w; (W.constSpec ma mb).IsSrc a) ↔
      a.1 = ma ∧ a.2 = w ∘ W.leftIx := by
  classical
  change (@Formula.Realize _ A (letI := constStructure (L₀ := L) w; inferInstance) _
    (if a.1 = ma then toConst W.eqLeftF else ⊥) a.2) ↔ _
  split_ifs with h
  · rw [realize_toConst, and_iff_right h, eqLeftF, Formula.realize_iInf]
    simp only [Formula.realize_equal, Term.realize_var, Sum.elim_inr, Sum.elim_inl]
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  · simp only [Formula.realize_bot, false_iff, not_and]
    exact fun h' => absurd h' h

theorem constSpec_isTgt (a : W.Node A) :
    (letI := constStructure (L₀ := L) w; (W.constSpec ma mb).IsTgt a) ↔
      a.1 = mb ∧ a.2 = w ∘ W.rightIx := by
  classical
  change (@Formula.Realize _ A (letI := constStructure (L₀ := L) w; inferInstance) _
    (if a.1 = mb then toConst W.eqRightF else ⊥) a.2) ↔ _
  split_ifs with h
  · rw [realize_toConst, and_iff_right h, eqRightF, Formula.realize_iInf]
    simp only [Formula.realize_equal, Term.realize_var, Sum.elim_inr, Sum.elim_inl]
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  · simp only [Formula.realize_bot, false_iff, not_and]
    exact fun h' => absurd h' h

theorem constSpec_reach (a b : W.Node A) :
    (letI := constStructure (L₀ := L) w; (W.constSpec ma mb).Reach a b) ↔
      W.ReachAt (w ∘ W.parIx) a b := by
  let := constStructure (L₀ := L) w
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih => exact ih.tail ((W.constSpec_step ma mb w c d).mp hcd)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail c d _ hcd ih => exact ih.tail ((W.constSpec_step ma mb w c d).mpr hcd)

/-- **The sentence says reachability** between the two endpoints. -/
theorem constSpec_accepts :
    (letI := constStructure (L₀ := L) w; (W.constSpec ma mb).Accepts A) ↔
      W.ReachAt (w ∘ W.parIx) (ma, w ∘ W.leftIx) (mb, w ∘ W.rightIx) := by
  let := constStructure (L₀ := L) w
  constructor
  · rintro ⟨u, v, hu, hv, huv⟩
    obtain ⟨hu1, hu2⟩ := (W.constSpec_isSrc ma mb w u).mp hu
    obtain ⟨hv1, hv2⟩ := (W.constSpec_isTgt ma mb w v).mp hv
    have := (W.constSpec_reach ma mb w u v).mp huv
    rwa [← hu1, ← hu2, ← hv1, ← hv2]
  · intro h
    exact ⟨_, _, (W.constSpec_isSrc ma mb w _).mpr ⟨rfl, rfl⟩,
      (W.constSpec_isTgt ma mb w _).mpr ⟨rfl, rfl⟩, (W.constSpec_reach ma mb w _ _).mpr h⟩

/-! ### The complement, with parameters -/

/-- **The complement of the walk between two endpoints**, with parameters:
the inductive-counting walk of `DescriptiveComplexity.TCCompl.complSpec` run
on the sentence with constants. -/
noncomputable def coSpec (ma mb : W.Mode) : TCSpec (withPar (L.sum Language.order) W.AtomPar) :=
  letI : LinearOrder (W.constSpec ma mb).pad.Mode := finiteLinearOrder _
  TCCompl.complSpec (W.constSpec ma mb).pad

/-- **The complement accepts exactly when the second endpoint is not
reached.** -/
theorem coSpec_accepts [Finite A] [Nonempty A] :
    (letI := constStructure (L₀ := L) w; (W.coSpec ma mb).Accepts A) ↔
      ¬W.ReachAt (w ∘ W.parIx) (ma, w ∘ W.leftIx) (mb, w ∘ W.rightIx) := by
  let := constStructure (L₀ := L) w
  let : LinearOrder (W.constSpec ma mb).pad.Mode := finiteLinearOrder _
  rw [coSpec, TCCompl.complSpec_accepts_iff, TCSpec.pad_accepts_iff]
  exact not_congr (W.constSpec_accepts ma mb w)

/-! ### The decider -/

/-- The variables of the walk's step, in the decider's. -/
def yesVar : (Fin W.k ⊕ Fin W.k) ⊕ Fin W.par →
    ((Fin W.k ⊕ Fin (W.coSpec ma mb).k) ⊕ (Fin W.k ⊕ Fin (W.coSpec ma mb).k)) ⊕ W.AtomPar
  | Sum.inl (Sum.inl i) => Sum.inl (Sum.inl (Sum.inl i))
  | Sum.inl (Sum.inr i) => Sum.inl (Sum.inr (Sum.inl i))
  | Sum.inr j => Sum.inr (W.parIx j)

/-- The variables of the complement's step, in the decider's. -/
def noVar : W.AtomPar ⊕ (Fin (W.coSpec ma mb).k ⊕ Fin (W.coSpec ma mb).k) →
    ((Fin W.k ⊕ Fin (W.coSpec ma mb).k) ⊕ (Fin W.k ⊕ Fin (W.coSpec ma mb).k)) ⊕ W.AtomPar
  | Sum.inl g => Sum.inr g
  | Sum.inr (Sum.inl i) => Sum.inl (Sum.inl (Sum.inr i))
  | Sum.inr (Sum.inr i) => Sum.inl (Sum.inr (Sum.inr i))

/-- The variables of the complement's source formula, read on the next tuple
of the decider's step. -/
def coSrcVar : W.AtomPar ⊕ Fin (W.coSpec ma mb).k →
    ((Fin W.k ⊕ Fin (W.coSpec ma mb).k) ⊕ (Fin W.k ⊕ Fin (W.coSpec ma mb).k)) ⊕ W.AtomPar
  | Sum.inl g => Sum.inr g
  | Sum.inr i => Sum.inl (Sum.inr (Sum.inr i))

/-- The variables of the complement's target formula, in the decider's
exit. -/
def coExitVar : W.AtomPar ⊕ Fin (W.coSpec ma mb).k →
    (Fin W.k ⊕ Fin (W.coSpec ma mb).k) ⊕ W.AtomPar
  | Sum.inl g => Sum.inr g
  | Sum.inr i => Sum.inl (Sum.inr i)

open Classical in
/-- **The decider of reachability** between two modes, at the two endpoints
and the parameters: from its start it either enters the walk at the first
endpoint and exits `yes` on standing at the second, or enters the complement
walk at one of its sources and exits `no` at one of its targets. The
coordinates of the idle branch are copied along. -/
@[reducible]
noncomputable def reachDecider (ma mb : W.Mode) : Decider L W.AtomPar where
  Mode := Option (W.Mode ⊕ (W.coSpec ma mb).Mode)
  Coord := Fin W.k ⊕ Fin (W.coSpec ma mb).k
  start := none
  step m n :=
    match m, n with
    | none, some (Sum.inl m) =>
        if m = ma then
          (Formula.iInf fun i : Fin W.k =>
            Term.equal (Term.var (Decider.nextVar (Sum.inl i))) (Term.var (Sum.inr (W.leftIx i)))) ⊓
            copyF (fun i : Fin (W.coSpec ma mb).k => Decider.curVar (Sum.inr i))
              (fun i => Decider.nextVar (Sum.inr i))
        else ⊥
    | none, some (Sum.inr c) =>
        (fromConst ((W.coSpec ma mb).src c)).relabel (W.coSrcVar ma mb) ⊓
          copyF (fun i : Fin W.k => Decider.curVar (Sum.inl i))
            (fun i => Decider.nextVar (Sum.inl i))
    | some (Sum.inl m), some (Sum.inl n) =>
        (W.step m n).relabel (W.yesVar ma mb) ⊓
          copyF (fun i : Fin (W.coSpec ma mb).k => Decider.curVar (Sum.inr i))
            (fun i => Decider.nextVar (Sum.inr i))
    | some (Sum.inr c), some (Sum.inr c') =>
        (fromConst ((W.coSpec ma mb).step c c')).relabel (W.noVar ma mb) ⊓
          copyF (fun i : Fin W.k => Decider.curVar (Sum.inl i))
            (fun i => Decider.nextVar (Sum.inl i))
    | _, _ => ⊥
  exit m o :=
    match m, o with
    | some (Sum.inl m), true =>
        if m = mb then
          Formula.iInf fun i : Fin W.k =>
            Term.equal (Term.var (Sum.inl (Sum.inl i))) (Term.var (Sum.inr (W.rightIx i)))
        else ⊥
    | some (Sum.inr c), false => (fromConst ((W.coSpec ma mb).tgt c)).relabel (W.coExitVar ma mb)
    | _, _ => ⊥

/-! #### Steps and exits -/

section Semantics

variable {ma mb}

theorem reachDecider_stepAt_none_inl (m : W.Mode)
    (t t' : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A) :
    (W.reachDecider ma mb).StepAt w (none, t) (some (Sum.inl m), t') ↔
      m = ma ∧ t' ∘ Sum.inl = w ∘ W.leftIx ∧ t' ∘ Sum.inr = t ∘ Sum.inr := by
  classical
  have hstep : (W.reachDecider ma mb).step none (some (Sum.inl m)) = if m = ma then
      (Formula.iInf fun i : Fin W.k =>
        Term.equal (Term.var (Decider.nextVar (Sum.inl i))) (Term.var (Sum.inr (W.leftIx i)))) ⊓
        copyF (fun i : Fin (W.coSpec ma mb).k => Decider.curVar (Sum.inr i))
          (fun i => Decider.nextVar (Sum.inr i))
      else ⊥ := rfl
  unfold Decider.StepAt
  rw [hstep]
  split_ifs with h
  · rw [Formula.realize_inf, Formula.realize_iInf, realize_copyF, and_iff_right h]
    simp only [Formula.realize_equal, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
    exact and_congr ⟨fun h => funext h, fun h i => congrFun h i⟩ Iff.rfl
  · simp only [Formula.realize_bot, false_iff, not_and]
    exact fun h' => absurd h' h

theorem reachDecider_stepAt_none_inr (c : (W.coSpec ma mb).Mode)
    (t t' : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A) :
    (W.reachDecider ma mb).StepAt w (none, t) (some (Sum.inr c), t') ↔
      (letI := constStructure (L₀ := L) w; (W.coSpec ma mb).IsSrc (c, t' ∘ Sum.inr)) ∧
        t' ∘ Sum.inl = t ∘ Sum.inl := by
  have hstep : (W.reachDecider ma mb).step none (some (Sum.inr c)) =
      (fromConst ((W.coSpec ma mb).src c)).relabel (W.coSrcVar ma mb) ⊓
        copyF (fun i : Fin W.k => Decider.curVar (Sum.inl i))
          (fun i => Decider.nextVar (Sum.inl i)) := rfl
  unfold Decider.StepAt
  rw [hstep, Formula.realize_inf, Formula.realize_relabel, realize_copyF]
  refine and_congr ?_ Iff.rfl
  have := realize_fromConst (L₀ := L) w ((W.coSpec ma mb).src c) (t' ∘ Sum.inr)
  refine Iff.trans (iff_of_eq (congrArg (Formula.Realize (M := A) _) (funext fun i => ?_))) this
  rcases i with i | i <;> rfl

theorem reachDecider_stepAt_inl_inl (m n : W.Mode)
    (t t' : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A) :
    (W.reachDecider ma mb).StepAt w (some (Sum.inl m), t) (some (Sum.inl n), t') ↔
      W.StepAt (w ∘ W.parIx) (m, t ∘ Sum.inl) (n, t' ∘ Sum.inl) ∧ t' ∘ Sum.inr = t ∘ Sum.inr := by
  have hstep : (W.reachDecider ma mb).step (some (Sum.inl m)) (some (Sum.inl n)) =
      (W.step m n).relabel (W.yesVar ma mb) ⊓
        copyF (fun i : Fin (W.coSpec ma mb).k => Decider.curVar (Sum.inr i))
          (fun i => Decider.nextVar (Sum.inr i)) := rfl
  unfold Decider.StepAt
  rw [hstep, Formula.realize_inf, Formula.realize_relabel, realize_copyF]
  refine and_congr (iff_of_eq (congrArg (Formula.Realize (M := A) (W.step m n))
    (funext fun i => ?_))) Iff.rfl
  rcases i with (i | i) | i <;> rfl

theorem reachDecider_stepAt_inr_inr (c c' : (W.coSpec ma mb).Mode)
    (t t' : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A) :
    (W.reachDecider ma mb).StepAt w (some (Sum.inr c), t) (some (Sum.inr c'), t') ↔
      (letI := constStructure (L₀ := L) w;
        (W.coSpec ma mb).Step (c, t ∘ Sum.inr) (c', t' ∘ Sum.inr)) ∧
        t' ∘ Sum.inl = t ∘ Sum.inl := by
  have hstep : (W.reachDecider ma mb).step (some (Sum.inr c)) (some (Sum.inr c')) =
      (fromConst ((W.coSpec ma mb).step c c')).relabel (W.noVar ma mb) ⊓
        copyF (fun i : Fin W.k => Decider.curVar (Sum.inl i))
          (fun i => Decider.nextVar (Sum.inl i)) := rfl
  unfold Decider.StepAt
  rw [hstep, Formula.realize_inf, Formula.realize_relabel, realize_copyF]
  refine and_congr ?_ Iff.rfl
  have := realize_fromConst (L₀ := L) w ((W.coSpec ma mb).step c c')
    (Sum.elim (t ∘ Sum.inr) (t' ∘ Sum.inr))
  refine Iff.trans (iff_of_eq (congrArg (Formula.Realize (M := A) _) (funext fun i => ?_))) this
  rcases i with i | (i | i) <;> rfl

theorem reachDecider_not_stepAt_none_none (t t' : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A) :
    ¬(W.reachDecider ma mb).StepAt w (none, t) (none, t') :=
  fun h => h

theorem reachDecider_not_stepAt_some_none (m : W.Mode ⊕ (W.coSpec ma mb).Mode)
    (t t' : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A) :
    ¬(W.reachDecider ma mb).StepAt w (some m, t) (none, t') := by
  rcases m with m | m <;> exact fun h => h

theorem reachDecider_not_stepAt_inl_inr (m : W.Mode) (c : (W.coSpec ma mb).Mode)
    (t t' : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A) :
    ¬(W.reachDecider ma mb).StepAt w (some (Sum.inl m), t) (some (Sum.inr c), t') :=
  fun h => h

theorem reachDecider_not_stepAt_inr_inl (c : (W.coSpec ma mb).Mode) (m : W.Mode)
    (t t' : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A) :
    ¬(W.reachDecider ma mb).StepAt w (some (Sum.inr c), t) (some (Sum.inl m), t') :=
  fun h => h

theorem reachDecider_exitAt_inl_true (m : W.Mode) (t : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A) :
    (W.reachDecider ma mb).ExitAt w (some (Sum.inl m), t) true ↔
      m = mb ∧ t ∘ Sum.inl = w ∘ W.rightIx := by
  classical
  have hexit : (W.reachDecider ma mb).exit (some (Sum.inl m)) true = if m = mb then
      Formula.iInf fun i : Fin W.k =>
        Term.equal (Term.var (Sum.inl (Sum.inl i))) (Term.var (Sum.inr (W.rightIx i)))
      else ⊥ := rfl
  unfold Decider.ExitAt
  rw [hexit]
  split_ifs with h
  · rw [Formula.realize_iInf, and_iff_right h]
    simp only [Formula.realize_equal, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  · simp only [Formula.realize_bot, false_iff, not_and]
    exact fun h' => absurd h' h

theorem reachDecider_not_exitAt_inl_false (m : W.Mode)
    (t : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A) :
    ¬(W.reachDecider ma mb).ExitAt w (some (Sum.inl m), t) false :=
  fun h => h

theorem reachDecider_exitAt_inr_false (c : (W.coSpec ma mb).Mode)
    (t : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A) :
    (W.reachDecider ma mb).ExitAt w (some (Sum.inr c), t) false ↔
      (letI := constStructure (L₀ := L) w; (W.coSpec ma mb).IsTgt (c, t ∘ Sum.inr)) := by
  have hexit : (W.reachDecider ma mb).exit (some (Sum.inr c)) false =
      (fromConst ((W.coSpec ma mb).tgt c)).relabel (W.coExitVar ma mb) := rfl
  unfold Decider.ExitAt
  rw [hexit, Formula.realize_relabel]
  have := realize_fromConst (L₀ := L) w ((W.coSpec ma mb).tgt c) (t ∘ Sum.inr)
  refine Iff.trans (iff_of_eq (congrArg (Formula.Realize (M := A) _) (funext fun i => ?_))) this
  rcases i with i | i <;> rfl

theorem reachDecider_not_exitAt_inr_true (c : (W.coSpec ma mb).Mode)
    (t : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A) :
    ¬(W.reachDecider ma mb).ExitAt w (some (Sum.inr c), t) true :=
  fun h => h

theorem reachDecider_not_exitAt_none (t : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A) (o : Bool) :
    ¬(W.reachDecider ma mb).ExitAt w (none, t) o := by
  cases o <;> exact fun h => h

/-! #### Lifting the two walks -/

/-- A path of the walk lifts to the `yes` branch. -/
theorem reachDecider_reachAt_of_reachAt {a b : W.Node A} (h : W.ReachAt (w ∘ W.parIx) a b)
    (r : Fin (W.coSpec ma mb).k → A) :
    (W.reachDecider ma mb).ReachAt w (some (Sum.inl a.1), Sum.elim a.2 r)
      (some (Sum.inl b.1), Sum.elim b.2 r) := by
  refine Relation.ReflTransGen.lift
    (fun c : W.Node A => (some (Sum.inl c.1), Sum.elim c.2 r)) (fun c d hcd => ?_) _ _ h
  exact (W.reachDecider_stepAt_inl_inl w c.1 d.1 _ _).mpr ⟨by simpa using hcd, rfl⟩

/-- A path of the complement lifts to the `no` branch. -/
theorem reachDecider_reachAt_of_coReach {a b : (W.coSpec ma mb).Node A}
    (h : letI := constStructure (L₀ := L) w; (W.coSpec ma mb).Reach a b) (l : Fin W.k → A) :
    (W.reachDecider ma mb).ReachAt w (some (Sum.inr a.1), Sum.elim l a.2)
      (some (Sum.inr b.1), Sum.elim l b.2) := by
  let := constStructure (L₀ := L) w
  refine Relation.ReflTransGen.lift
    (fun c : (W.coSpec ma mb).Node A => (some (Sum.inr c.1), Sum.elim l c.2))
    (fun c d hcd => ?_) _ _ h
  exact (W.reachDecider_stepAt_inr_inr w c.1 d.1 _ _).mpr ⟨by simpa using hcd, rfl⟩

/-- What the decider may have reached: its start, a node of the walk reached
from the first endpoint, or a node of the complement reached from one of its
sources. -/
def ReachInv (t : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A) (c : (W.reachDecider ma mb).Node A) :
    Prop :=
  c = (none, t) ∨
    (∃ (m : W.Mode) (t' : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A), c = (some (Sum.inl m), t') ∧
      W.ReachAt (w ∘ W.parIx) (ma, w ∘ W.leftIx) (m, t' ∘ Sum.inl)) ∨
    (∃ (d : (W.coSpec ma mb).Mode) (t' : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A),
      c = (some (Sum.inr d), t') ∧
      (letI := constStructure (L₀ := L) w;
        ∃ s : (W.coSpec ma mb).Node A, (W.coSpec ma mb).IsSrc s ∧
          (W.coSpec ma mb).Reach s (d, t' ∘ Sum.inr)))

theorem reachInv_of_reachAt (t : Fin W.k ⊕ Fin (W.coSpec ma mb).k → A)
    {c : (W.reachDecider ma mb).Node A} (h : (W.reachDecider ma mb).ReachAt w (none, t) c) :
    W.ReachInv w t c := by
  let := constStructure (L₀ := L) w
  refine reach_invariant (P := W.ReachInv w t) (fun a b ha hab => ?_) h (Or.inl rfl)
  obtain ⟨mb', tb⟩ := b
  rcases ha with rfl | ⟨m, t', rfl, hr⟩ | ⟨d, t', rfl, s, hs, hr⟩
  · rcases mb' with _ | (m | d)
    · exact absurd hab (W.reachDecider_not_stepAt_none_none w t tb)
    · obtain ⟨rfl, hl, -⟩ := (W.reachDecider_stepAt_none_inl w m t tb).mp hab
      refine Or.inr (Or.inl ⟨m, tb, rfl, ?_⟩)
      rw [hl]
    · obtain ⟨hs, -⟩ := (W.reachDecider_stepAt_none_inr w d t tb).mp hab
      exact Or.inr (Or.inr ⟨d, tb, rfl, _, hs, Relation.ReflTransGen.refl⟩)
  · rcases mb' with _ | (n | d)
    · exact absurd hab (W.reachDecider_not_stepAt_some_none w _ t' tb)
    · obtain ⟨hs, -⟩ := (W.reachDecider_stepAt_inl_inl w m n t' tb).mp hab
      exact Or.inr (Or.inl ⟨n, tb, rfl, hr.tail hs⟩)
    · exact absurd hab (W.reachDecider_not_stepAt_inl_inr w m d t' tb)
  · rcases mb' with _ | (n | d')
    · exact absurd hab (W.reachDecider_not_stepAt_some_none w _ t' tb)
    · exact absurd hab (W.reachDecider_not_stepAt_inr_inl w d n t' tb)
    · obtain ⟨hs', -⟩ := (W.reachDecider_stepAt_inr_inr w d d' t' tb).mp hab
      exact Or.inr (Or.inr ⟨d', tb, rfl, s, hs, hr.tail hs'⟩)

variable [Finite A] [Nonempty A]

/-- **The decider decides reachability** between its two modes, at the two
endpoints and the parameters. -/
theorem decides_reachDecider :
    (W.reachDecider ma mb).Decides w
      (W.ReachAt (w ∘ W.parIx) (ma, w ∘ W.leftIx) (mb, w ∘ W.rightIx)) := by
  let := constStructure (L₀ := L) w
  intro t
  constructor
  · constructor
    · rintro ⟨c, hc, he⟩
      rcases W.reachInv_of_reachAt w t hc with rfl | ⟨m, t', rfl, hr⟩ | ⟨d, t', rfl, -⟩
      · exact absurd he (W.reachDecider_not_exitAt_none w t true)
      · obtain ⟨rfl, hr'⟩ := (W.reachDecider_exitAt_inl_true w m t').mp he
        rwa [hr'] at hr
      · exact absurd he (W.reachDecider_not_exitAt_inr_true w d t')
    · intro h
      refine ⟨(some (Sum.inl mb), Sum.elim (w ∘ W.rightIx) (t ∘ Sum.inr)), ?_,
        (W.reachDecider_exitAt_inl_true w mb _).mpr ⟨rfl, by simp⟩⟩
      refine Relation.ReflTransGen.head ((W.reachDecider_stepAt_none_inl w ma t
        (Sum.elim (w ∘ W.leftIx) (t ∘ Sum.inr))).mpr ⟨rfl, by simp, by simp⟩) ?_
      exact W.reachDecider_reachAt_of_reachAt w (a := (ma, w ∘ W.leftIx))
        (b := (mb, w ∘ W.rightIx)) h (t ∘ Sum.inr)
  · rw [← W.coSpec_accepts ma mb w]
    constructor
    · rintro ⟨c, hc, he⟩
      rcases W.reachInv_of_reachAt w t hc with rfl | ⟨m, t', rfl, -⟩ | ⟨d, t', rfl, s, hs, hr⟩
      · exact absurd he (W.reachDecider_not_exitAt_none w t false)
      · exact absurd he (W.reachDecider_not_exitAt_inl_false w m t')
      · exact ⟨s, _, hs, (W.reachDecider_exitAt_inr_false w d t').mp he, hr⟩
    · rintro ⟨s, s', hs, hs', hss'⟩
      refine ⟨(some (Sum.inr s'.1), Sum.elim (t ∘ Sum.inl) s'.2), ?_,
        (W.reachDecider_exitAt_inr_false w s'.1 _).mpr (by simpa using hs')⟩
      refine Relation.ReflTransGen.head ((W.reachDecider_stepAt_none_inr w s.1 t
        (Sum.elim (t ∘ Sum.inl) s.2)).mpr ⟨by simpa using hs, by simp⟩) ?_
      exact W.reachDecider_reachAt_of_coReach w hss' (t ∘ Sum.inl)

end Semantics

end ParamTCSpec

/-! ### The deciders of a family -/

namespace TCFamily

variable {L : Language.{0, 0}} (F : TCFamily (L.sum Language.order))

/-- **The reachability deciders of a family**: one per relation variable of
its block. -/
noncomputable def reachDeciders (q : F.block.ι) : Decider L (Fin (F.block.arity q)) :=
  (F.spec q.1).reachDecider q.2.1 q.2.2

/-- **The deciders decide the family's reachability relations.** -/
theorem decides_reachDeciders (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
    (q : F.block.ι) (w : Fin (F.block.arity q) → A) :
    (F.reachDeciders q).Decides w (F.reachAssign A q w) :=
  (F.spec q.1).decides_reachDecider w

end TCFamily

end DescriptiveComplexity
